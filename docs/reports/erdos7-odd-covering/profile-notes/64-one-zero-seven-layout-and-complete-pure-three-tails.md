[Index](../marked_head_profile.md) · [Endpoint geometry](59-endpoint-linear-source-deletion-bound.md) · [Complete ordered pairs](62-endpoint-square-from-cylinder-intersections.md) · [Six-label coherence](63-six-original-labels-strengthen-the-endpoint-square.md)

# One zero-seven layout and complete pure-three tails give square469/100

For the endpoint class of profiles59–63, every independently labelled
complete original357 test A satisfies

    limsup integral_survivor A^2<=469/100.               (1)

Thus the current square barrier45 has absolute margin

    liminf [45*S-integral_survivor A^2]>=103/50.

The endpoint hypotheses are source parameters tending to vertex404,
actual normalized survivor mass tending to3/20, and shallow carrier
mixture tending to(0,1). Every original test label may choose its own
residue, and the choices may change along the sequence.

Two changes give(1): retaining all pure3 test depths inside one
coherent old-coordinate block, and keeping the same zero-seven
shallow layout in its surviving cost and cross-depth source norm.
All numerical inequalities used for the final bound are exact
rational comparisons. No numerical square root is a proof input.
This is an ordinary endpoint theorem, not a quantitative neighborhood,
global K bound, physical denominator estimate, or Lean result.

## 1. Extend the six-label block by all pure3 depths

At each seven depth use the old-coordinate block

    X=B+T,
    B=load of original labels{1,3,9,5,15,45},
    T=sum_(a>=3)1_(J_a),

where J_a is the arbitrarily chosen original cylinder of modulus3^a.
The six-label load B has one of the12500 layouts enumerated in
profile63. Denote its value on cell l and first-five slot j by B_lj.
Every B_lj is at least1.

The deep test cylinders need not be nested. Pointwise,

    T^2<=sum_(a>=3)(2a-5)*1_(J_a),

because a diagonal pair contributes once and there are a-3 earlier
deep labels, each of whose two ordered intersections is at most
1_(J_a). Consequently

    X^2-B^2<=sum_(a>=3)w_a*1_(J_a),
    w_a(l,j)=2*B_lj+2a-5>=3.                       (2)

We bound this complete tail separately for the actual surviving
marginal mu and the raw35 source Lambda, while retaining the same B.

## 2. Weighted deletion on every deep test cylinder

Use the five slots P,A,Beta,Q,H from profile59. Before the additional
late35 deletion, the raw source mass on a pure3 cylinder J in cell l
times a slot j is eta(J)*c_lj, with

| Cells | P | A | Beta | Q | H |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0,1 | 0 | 1/5 | 1/5 | 3/20 | 1/5 |
| 2 | 0 | 0 | 0 | 1/20 | 1/5 |
| 3,4 | 0 | 0 | 1/5 | 1/10 | 1/5 |

Dropping late deletion is an upper bound for any nonnegative slot
weight. Retaining the four complete forbidden-cofactor families
3,9,5,15 from profile59 multiplies these coefficients by

    k_lj=c_lj*[1-(1_root0+1_(l=1)+1_(j=H)
                                     +1_(root1 and j=H))/5].

There is also a complete deletion tail that is distinct from these
four families. Saturated original cofactors5^b and3*5^b, b>=2,
have globally source-free five-coordinate cylinders. Such a cylinder
cannot lie in P,A, or Beta: each of those slots has positive source
loss on a ternary set of positive eta measure. It therefore lies
in Q or H. On every pure3 test cylinder J in cell l their combined
virtual deleted mass is exactly

    eta(J)*ell_l, ell_l=(1+1_root1)/100.

Indeed sum_(b>=2)5^(-b)=1/20 and sum_(e>=1)u_e=1/5.
At endpoint saturation actual deletion equals the complete virtual
cofactor measure. The b>=2 labels are different from3,9,5,15, so
their measure may be added to the four selected contributions.
No disjointness of their old-coordinate projections is assumed.

For any nonnegative weight w constant on the five slots of cell l,

    integral_(J) w dmu
      <=eta(J)*[sum_j k_lj*w_j-ell_l*min(w_Q,w_H)].  (3)

Every k_lj is nonnegative and k_lQ+k_lH>=ell_l. Thus the bracket
is nonnegative. In particular applying(3) to w_a from(2) allows
the further upper bound eta(J)<=3^(-a). This sign check is necessary
after subtracting the weighted deletion credit.

The raw source has the simpler bound

    integral_(J) w_a dLambda
       <=3^(-a)*sum_j c_lj*w_a(l,j).               (4)

These inequalities are valid for every original deep test residue.
A cylinder outside the surviving ternary cells contributes zero.

## 3. Complete affine tails attached to each shallow layout

For a fixed B define five affine functions for each measure:

    z_l(a)=sum_j k_lj*(2*B_lj+2a-5)
                     -ell_l*(2*min(B_lQ,B_lH)+2a-5),
    r_l(a)=sum_j c_lj*(2*B_lj+2a-5).

Their slopes are nonnegative and their values are nonnegative for
all a>=3. The complete deep contributions in(2) are bounded by

    T_mu(B)=sum_(a>=3)3^(-a)*max_l z_l(a),
    T_Lambda(B)=sum_(a>=3)3^(-a)*max_l r_l(a).      (5)

These are exact infinite sums of the stated upper envelopes. They
are not truncated searches. Among finitely many affine lines, choose
one with largest slope and then largest intercept. Past all of its
crossing points it dominates every other line. Before that integer
entrance evaluate the finite maximum explicitly, and use

    sum_(a>=n)3^(-a)=1/(2*3^(n-1)),
    sum_(a>=n)a*3^(-a)=(2n+1)/(4*3^(n-1))

for the remaining affine tail. Across all12500 layouts and both
measures, the largest such entrance is10; all depths beyond it
remain included by these formulas.

Let Z_6(B) be the certified surviving upper bound on B^2-1 in
profile63, with its entry, row and total-mass constraints. Let R_6(B)
be the maximum of the two exact raw-source endpoint values for B^2.
Set

    Z(B)=Z_6(B)+T_mu(B),
    R(B)=R_6(B)+T_Lambda(B).

For every actual expanded test block with shallow layout B,

    integral_mu(X^2-1)<=Z(B),
    integral_Lambda X^2<=R(B).                    (6)

The checker revalidates each of profile63's12500 feasible primal/dual
equalities before adding the two tails. The resulting maxima are

    max_B Z(B)=6068947/3936600,
    Rstar=max_B R(B)=212153/87480.                (7)

The zero marginal and raw maxima occur at different shallow layouts:
the former concentrates the three first-five test labels on Beta,
the latter on H, both with root1 and cell4. In the next step each
layout keeps its own pair Z(B),R(B).

## 4. One common B0 controls zero and cross-seven contributions

Let X_e be the expanded old-coordinate test block at seven depth e.
Only its zero-seven block X_0 has a surviving cost directly bounded
by Z(B_0). Its raw source square is simultaneously bounded by R(B_0).
Every positive-depth block has raw source square at most Rstar.

For each ordered pair of seven depths, the original seven-cylinder
intersection is at most u_max(e,f). This holds separately for each
old-coordinate pair, even if all original seven residues differ.
After summing old labels, Cauchy-Schwarz on the same Lambda gives

    integral_Lambda X_0*X_e<=sqrt(R(B_0)*Rstar), e>0,
    integral_Lambda X_e*X_f<=Rstar, e,f>0.         (8)

For e=f the second inequality is just the square bound. For unequal
depths it permits entirely independent original residues. The old
unit in each block remains present; at positive depth it is the
old-coordinate projection of the pure7 test label.

The total cap weights for these disjoint depth-pair classes are

    pairs(0,e),(e,0), e>=1: 2*sum_e u_e=2/5,
    pairs e,f>=1: sum_(t>=1)(2t-1)*u_t=4/15.

Thus the replaced expanded-head pair contribution, excluding only
the global unit-unit pair, is at most

    max_B[Z(B)+(2/5)*sqrt(R(B)*Rstar)]+(4/15)*Rstar. (9)

Keeping the same B in the two terms inside the maximum is the
additional constraint. Separately maximizing Z and R loses it.

## 5. A purely rational certificate for469/100

The old cap budgets in profile62 for this expanded head are

    zero-seven nonconstant: 1001/600,
    raw old-coordinate:     107/40.

To check the additional deep-label accounting, the pure3 lcm of
depth a>=3 has2a+1 ordered pairs from pure3 labels, and there are
six more ordered pairs between this depth and{5,15,45}. Their
complete extra caps are

    zero: (11/20)*(4/9)+(6/5)*(1/18)=14/45,
    raw:  (3/4)*(4/9)+(6/5)*(1/18)=2/5.

Adding these to profile63's head budgets gives the two displayed
values. The global unit-unit pair is excluded only from the zero
budget. All remaining ordered pairs have unchanged total bound

    E=4559/900-[1001/600+(2/3)*(107/40)].

Define the rational threshold

    K=469/100-E-(4/15)*Rstar=3187861/1312200.

For every one of the12500 layouts the checker verifies exactly

    K-Z(B)>=0,
    [(5/2)*(K-Z(B))]^2-R(B)*Rstar>=0.             (10)

The minimum second expression over the complete layout space is

    8715944851/619872782400>0.

Equation(10), with its sign condition, proves
Z(B)+(2/5)*sqrt(R(B)*Rstar)<=K without evaluating a square root.
Combining this with(9) and the unchanged remainder E proves(1).
The signed margin is45*(3/20)-469/100=103/50.

No correction is deducted from an already strengthened block twice:
this calculation replaces exactly the expanded head's ordered pairs
inside profile62's full sum. Every other pair retains its old cap.

## 6. Tails, verification, and an auxiliary third moment

All pure3 depths are retained in(5), all positive-seven depth pairs
in(8)–(9), and all other original labels in the unreplaced remainder.
For finite source families approaching the endpoint, profile62's
uniform quadratic tail estimate applies unchanged: original ordered
pairs outside a finite exponent box are dominated by a summable
polynomial times reciprocal prime powers. The labelwise diagonal
subsequence and convergence of finite test integrals therefore pass
the exact endpoint inequality to the limsup in(1).

The [standard-library checker](../frontier/endpoint_square_common_pure3.py)
reconstructs the pinned preceding cap tables, all12500 feasible
primal/dual equalities, all25000 affine tails, and all12500 rational
comparisons(10). The [certificate](../certificates/source_norms/endpoint_square_common_pure3.json)
contains the extrema, exact minimum slack, controlling layouts,
one common-layout witness, and deterministic hashes of the complete
case collections. It stores no per-case transcript.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_square_common_pure3.py --check
```

The script is read-only unless `--output PATH` is supplied; all
required checks remain active under -O. Finite enumeration here
exhausts a specified shallow layout space. The universal original
label, weighted-deletion, infinite-tail and limiting claims are
the ordinary arguments above.

An auxiliary consequence of profile62's ordered-r-tuple formula,
using r=3 and the same profile59 cylinder caps, is

    limsup integral_survivor A^3<=3874891/57600.

The multiplicity at exponent a is(a+1)^3-a^3=3a^2+3a+1; complete
polynomial-geometric sums give the displayed value. The corresponding
uniform cubic tail estimate proves the same approaching-family
statement. This auxiliary bound is not used in the proof of469/100
and is not claimed as a numerator improvement here.
