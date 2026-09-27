[Index](../../marked_head_profile.md) · [Original mixture](404-a-sharper-common-law-and-its-witness-choice-boundary.md) · [Different stationary recipe](407-limits-of-stationary-row-mixtures-and-finite-signature-summaries.md)

# Choosing the coefficient from the witnesses cannot meet the finite target

For every height `K>=1`, one fixed admissible source and one fixed set
of full-five and pair-ternary component laws defeat **every** coefficient
in the mixture recipe of report 404. The coefficient may depend on the
entire source, all component witnesses, and the height. Two actual
original-divisor layouts already force a value above the finite target
`2t_K`.

This is an ordinary analytic proof with exact checks, not Lean
certification. It rules out adjusting the coefficient of these fixed
components. It does not rule out choosing different components or an
arbitrary law on the same source. The lower bound proved here is below
six at each finite height; it does not settle whether an adaptive
coefficient can always attain the weaker ceiling six.

## The same actual components and two literal layouts

Use report 404's existing `sharpness_source(K)` without changing its
geometry. Let `F_K={0,1,2,3,4}^K` and `T_K={0,1,2}^K`, interpreted
as lowest-digit-first seven-adic residues. The uniform full-tree law
`mu` labels root column zero by row one and the other four columns
by row two. Its row distribution is `(1/5,4/5,0,0)`.

The six actual pair laws use `T_K`, labelled by row one when the pair
contains one, by row two for pairs `23,24`, and by row three for `34`.
Their omitted-row weighting from 404 gives

    omega = (8/15) Unif({1} x T_K)
          + (2/15) Unif({2} x T_K)
          + (1/3)  Unif({3} x T_K).

Let the source be the union of all these actual component supports.
It has the full five-tree and all six pair ternary trees. An unused
row-four point can be added if four active source rows are required;
this leaves every component law below unchanged.

For `0<=alpha<=1`, put `nu_alpha=alpha*mu+(1-alpha)*omega`. The law
is chosen before the phases. At every original divisor `d|5*7^K`,
including one, choose the residue of the indicated CRT centre:

* Layout A: row one, seven-adic coordinate zero.
* Layout B: row two, seven-adic coordinate one (low digit one, all
  later digits zero).

These are two allowed members of the full independent-phase game.
Using aligned layouts for a lower bound imposes no alignment restriction
on the maximum over all original phases.

Write

    S_f = sum_(j=0)^K (2j+1)5^-j
        = 15/8-(4K+7)/(8*5^K),
    S_q = sum_(j=0)^K (2j+1)3^-j
        = 3-(K+2)3^-K = t_K.

For an aligned layout, the square expansion contributes one pure/pure
and three row-constrained intersections at every maximal depth `j`.
Under `mu`, both selected positive-depth cylinders lie in the selected
row and have mass `5^-j`. At depth zero the selected row masses are
respectively `1/5` and `4/5`. Thus the two `mu` costs are
`4S_f-12/5` and `4S_f-3/5`.

Under `omega`, every selected pure prefix has mass `3^-j`, while
the selected row masses are `8/15` and `2/15`. Its two costs are
therefore `13S_q/5` and `7S_q/5`. Consequently the actual expectations
are exactly

    L_A(alpha)=4alpha S_f+(13/5)(1-alpha)S_q-12alpha/5,
    L_B(alpha)=4alpha S_f+(7/5)(1-alpha)S_q-3alpha/5.       (AC1)

In particular `Gamma_K(nu_alpha)>=max(L_A(alpha),L_B(alpha))`.

## Exact optimization of these two lower bounds

The slope of `L_A` is negative. It is `-6/5` at `K=1`; adding the
depth-`j` term, `j>=2`, changes it by
`(2j+1)(4*5^-j-(13/5)3^-j)<0`. The slope of `L_B` is positive:
`S_f>=8/5` and `S_q<3` give it a lower bound strictly above `8/5`.

Their difference and unique intersection in `[0,1]` are

    L_A-L_B=(6/5)(1-alpha)S_q-(9/5)alpha,
    alpha_* = 2S_q/(3+2S_q).

The decreasing and increasing lines therefore give

    min_(0<=alpha<=1) max(L_A(alpha),L_B(alpha))
      = M_K := S_q(8S_f+3)/(3+2S_q).                    (AC2)

This optimizes only the two displayed layout expectations, not the
complete functional `Gamma_K`.

Subtracting the finite target yields

    M_K-2t_K
      = S_q/(3+2S_q)
        * [4(K+2)3^-K-(4K+7)5^-K] > 0.                (AC3)

Indeed `3^-K>5^-K` and `4(K+2)>4K+7` for `K>=1`.
Thus for every such height and every coefficient, the same fixed
component segment fails the required finite comparison.

There is also one two-layout adversarial distribution that works
against every coefficient in the segment. If `s_A<0<s_B` are the two
slopes, assign layout A weight `s_B/(s_B-s_A)` and B weight
`-s_A/(s_B-s_A)`. The weighted slope is zero, so its cost is exactly
`M_K` under every `nu_alpha`. This is a certificate on the specified
segment of laws, not a dual certificate against every probability on
the full source.

For example, at heights one and two the lower bounds are `158/35`
and `2001/365`, with target gaps `18/35` and `1219/3285`.
On the other hand,

    M_K < 18S_q/(3+2S_q) < 6,
    lim_(K->infty) M_K=6.

The finite gap in AC3 is essential. Report 404's two different families
already force a value above six for every **fixed** coefficient at some height.
AC1--AC3 instead use one fixed family of components to obstruct even
a witness-dependent coefficient at the exact finite target. Neither
statement proves a source-minimax obstruction or unrestricted Erdős #7.

## Exact reproduction

[`adaptive_coefficient_segment_obstruction.py`](../../frontier/cover-geometry/adaptive_coefficient_segment_obstruction.py)
reuses the source constructor from report 404 and evaluates both
original layouts directly on the actual component probabilities.
Its general segment checker accepts two actual probabilities on one
source and two literal layouts, then computes the exact minimum of
the maximum of their two affine expectations. It keeps the target and
the resulting segment lower bound separate from a source-minimax claim.

Run from the repository root:

    python3 docs/reports/erdos7-odd-covering/frontier/cover-geometry/adaptive_coefficient_segment_obstruction.py
    python3 -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/adaptive_coefficient_segment_obstruction.py

The all-height assertion follows from AC1--AC3; finitely many checked
heights do not supply its quantifier.
