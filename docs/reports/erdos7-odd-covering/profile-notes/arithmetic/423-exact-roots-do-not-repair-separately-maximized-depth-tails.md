[Index](../../marked_head_profile.md) · [Actual profile bound](421-single-surplus-sources-admit-a-common-law-beyond-fast-decay.md) · [Unrestricted component roots](422-free-root-row-pair-laws-control-recursive-seed-sources.md)

# Exact roots do not repair separately maximized depth tails

Keeping the actual root joint table removes the shallow row-relabel cost
from 422, but does not make the resulting certificate complete. There is
an admissible actual source at every height K>=2, with a full law whose
non-row-1 mass is only 1/25, for which **every** mixture coefficient fails
the exact-root plus actual-depth-profile certificate. At K=2, the same
full/pair components nevertheless give an actual common law satisfying the
original independent-phase target. This is a counterexample to completeness
of that sufficient certificate, not to the sources or their minimax target.

All statements below are ordinary analytic results with exact finite
controls; no Lean certification or resolution of unrestricted Erdős #7
is claimed. The probabilities are fixed before all original phases.

## The actual root and the remaining tail certificate

Retain the original divisors 7^j and 5*7^j, 0<=j<=K, including 1 and 5.
Write Gamma_K(nu) for the maximum expected squared load over their fully
independent phases, and 2t_K=6-2(K+2)3^-K. For one actual law nu define

    R(nu)=max_(a,c,s,d) E_nu (1+[r=a]+[y=c mod7]+[r=s,y=d mod7])^2,
    p_j(u)=nu(Y=u mod7^j),       q_(j,r)(u)=nu(row=r,Y=u mod7^j),
    A_(j,r)=max_u[p_j(u)+q_(j,r)(u)],
    Z_(j,r)=max_u q_(j,r)(u),    B_j=max_r[A_(j,r)+2Z_(j,r)].

The root maximum includes all five row residues and all seven column
residues. Report 421's depth-pair argument, applied only when the maximum
depth is at least two, gives the sufficient certificate

    Gamma_K(nu) <= C_K(nu)
      := R(nu)+sum_(j=2)^K(2j+1)B_j.              (C1)

All shallow/deep cross terms are included: 2j+1 is the number of ordered
depth pairs whose maximum is j. Only the four-label root square is removed
from that shell count. This is a direct reuse of the existing profile bound.

Similarly, for 422's actual law

    nu_alpha=alpha mu+((1-alpha)/3)(eta_23+eta_24+eta_34),

the same-Y comparison can be confined to those deeper terms. With
D_j=max_u mu(row!=1,Y=u mod7^j), and 0<=alpha<=50/77, it yields

    Gamma_K(nu_alpha)
      <=R(nu_alpha)
        +sum_(j=2)^K(2j+1)[alpha 5^-j+3(1-alpha)3^-j+3alpha D_j].   (C2)

The coefficient restriction ensures alpha 5^-j<=2(1-alpha)3^-j/3 for
j>=2, exactly as in 422. No D_0 or D_1 is paid in C2. Root information
has been retained; the remaining independent maximization across depths
is a separate loss. The counterexample below applies even to C1, which
uses the actual deeper profiles rather than their transported upper bounds.

## A single actual source and its fixed components at every height

For b in {3,5} put

    F_(b,K)={sum_(j=0)^(K-1) d_j7^j : 0<=d_j<b}.

For K>=2 let mu be uniform on F_(5,K), with row label

    r(y)=2 if y=0 mod49, and r(y)=1 otherwise.

Let tau_r be uniform on {r} times F_(3,K), for r=2,3. Define

    S_K=supp(mu) union supp(tau_2) union supp(tau_3),
    eta_23=eta_24=tau_2,       eta_34=tau_3.        (C3)

These are actual supported probabilities, with full-prefix caps 5^-j and
pair-prefix caps 3^-j. Their pair row supports are exactly as permitted;
a pair probability need not put positive mass in both allowed rows.
The full projection contains its complete five-tree. Rows 2 and 3 each
contain a complete ternary tree. Row 1 also contains one: take root columns
1,2,3 and ternary digits thereafter, thereby avoiding the deleted 00 prefix.
Every one of the six row pairs therefore has a complete ternary projection
tree, including pair 14. Thus S_K is admissible, although no sharp-minimum
cardinality claim is made. Its full law has mu(row!=1)=1/25 at every height.

The law under test remains

    nu_alpha=alpha mu+(2(1-alpha)/3)tau_2+((1-alpha)/3)tau_3,
    0<=alpha<=1.                                  (C4)

Only its coefficient varies; its components do not depend on any phase.

## Every coefficient fails the actual-root/profile certificate

Write T_(b,K)=sum_(j=2)^K(2j+1)b^-j. At depth j>=2 the prefix zero lies
entirely in row 2 for the full component and belongs to both ternary
components. Consequently the actual profiles in C1 satisfy exactly

    B_j(nu_alpha)=4alpha 5^-j+3(1-alpha)3^-j.      (C5)

Indeed at that prefix row 2 attains both A_(j,2) and Z_(j,2), with values
2alpha 5^-j+(5/3)(1-alpha)3^-j and
alpha 5^-j+(2/3)(1-alpha)3^-j. The component caps bound every other
prefix and row by their resulting C5 value.

Two literal root layouts supply simultaneous lower bounds on R:

    (a,c,s,d)=(1,1,1,1):  2+(107/25)alpha,
    (a,c,s,d)=(2,0,2,0):  6-(98/25)alpha.        (C6)

After adding the C5 tail, the first affine function is strictly increasing
in alpha, since its slope is at least 107/25-3>0. The second is strictly
decreasing, since its slope is at most -98/25+4(11/40)<0. Their intersection
is alpha=20/41. It follows for every coefficient that

    C_K(nu_alpha)>=M_K
      :=838/205+(80/41)T_(5,K)+(63/41)T_(3,K).    (C7)

This is also the exact minimum of C_K over alpha. At the crossing, the root
joint masses, multiplied by 615, are

    row 1: 48 60 60 60 60 0 0
    row 2: 82 70 70  0  0 0 0
    row 3: 35 35 35  0  0 0 0
    row 4:  0  0  0  0  0 0 0.

Direct substitution in the four root indicators gives the following
maxima over c,d, multiplied by 615; a indexes rows and s indexes columns:

    (2514 2480 2269 2094)
    (2216 2514 2115 1940)
    (1795 1905 1740 1495)
    (1410 1520 1285 1110).

An absent row-zero phase is dominated by an actual-row phase with the
same column. Hence R=2514/615=838/205. This table does not depend on K;
the retained program also checks all 1,225 root layouts directly.

Using T_(5,K)=11/40-(4K+7)/(8*5^K) and
T_(3,K)=1-(K+2)/3^K, the exact certificate excess is

    M_K-2t_K
      =33/205+(19/41)(K+2)3^-K-(10/41)(4K+7)5^-K
      >3/205,                    K>=2.          (C8)

For the strict bound, (4K+7)5^-K decreases from 3/5 at K=2; drop the
positive ternary term. The certificate minimum tends to 1263/205>6.
Thus finer arithmetic resolution and optimization of alpha cannot repair
this particular separation into an exact root and independent depth maxima.

## The same components pass the original game at height two

At K=2 choose alpha=2150/4013 in C4. Its 42 positive integer weights,
with common denominator 4013, have the following complete description:

* Each of the 24 row-1 full-tree points has weight 86.
* The row-2 point y=0 has weight 224.
* The other eight row-2 ternary points have weight 138 each.
* Each of the nine row-3 ternary points has weight 69.

The exact original independent-phase maximum is

    Gamma_2(nu_(2150/4013))=20475/4013,
    2t_2-Gamma_2=323/36117>0.                    (C9)

Both layouts with phases

    (a_1,a_5,a_7,a_35,a_49,a_245)
       =(0,1,0,7,0,147), (0,2,0,7,0,147)

attain C9. The matching upper bound is an exhaustive exact finite
calculation on all original phases, with this reduction: for each of
the 1,225 root layouts let l_0 be its pointwise four-label load, and put

    A_u=sum_r w_(r,u)(2l_0(r,u)+1),
    B_(r,v)=w_(r,v)(2l_0(r,v)+1).

The best two depth-two labels have additional numerator

    max_(u,r,v) [A_u+B_(r,v)+2w_(r,v)[u=v]].     (C10)

Here u ranges over all 49 pure phases, while (r,v) ranges over the actual
positive mixed cells. An empty mixed phase has zero gain and is dominated
by a positive cell. Thus C10 permits unrelated pure and mixed phases and
omits none that could maximize the load. The program evaluates it using
integer arithmetic, checks an attaining literal CRT layout, and independently
compares with the existing original-label tree DP from 416.

By C8, C1 fails for this very same law, as it does for every coefficient
of these fixed components. Hence the obstruction is a genuine information
loss in the sufficient certificate; it is not merely a failed component
choice. Neither C9 nor the coefficient in it is asserted to be the
minimax of all supported probabilities on S_2.

## The sources themselves have an all-height successful law

To separate the certificate obstruction from source failure at every
height, let mu_1 be mu conditioned on row 1, whose original mass is 24/25,
and take the actual probability

    zeta=(mu_1+tau_2+tau_3)/3.                   (C11)

Its exact profiles from 421 are

    B_0=2,       B_1=5/8,
    B_j=(25/72)5^-j+(5/3)3^-j,     j>=2.       (C12)

The root marginal of mu_1 has mass 1/6 in column zero and 5/24 in each
column 1,...,4. The other two rows have ternary root mass 1/3 in each
of columns 0,1,2. These values prove the first two entries. At depth j>=2,
a prefix beginning with digit 1 attains both maxima for row 2 or row 3.
The row-1 expression is no larger because 3^-j>=(25/24)5^-j.
The existing all-phase profile theorem therefore yields

    Gamma_K(zeta)<=31/8+(25/72)T_(5,K)+(5/3)T_(3,K).             (C13)

Its margin below 2t_K is 13/54 at K=2 and strictly increases: the
next-depth target increment minus the C13 increment is

    (2K+3)[(1/3)3^-(K+1)-(25/72)5^-(K+1)]>0.

Thus every S_K has an actual common law with uniform margin at least
13/54. C11 is used to establish the scope of the obstruction, while C9
already proves certificate incompleteness without changing components.

## Verification and remaining interface

[`actual_root_tail_obstruction.py`](../../frontier/cover-geometry/actual_root_tail_obstruction.py)
checks the actual sources at K=2,3,4, all seven projection-tree conditions,
component support and prefix caps, the exact profiles and root lines,
the coefficient minimum and its strict excess, and C11's successful
profiles. Its separate height-two calculation proves C9 by C10 and a
literal CRT witness, then compares with the existing independent tree DP.
Input failures use explicit exceptions, which remain active under `-O`.

Run from the repository root:

    python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual_root_tail_obstruction.py
    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual_root_tail_obstruction.py

The unbounded-height conclusions follow from C3--C8 and C11--C13, not
from extending the finite checks by induction without a proof. The
remaining all-source problem requires additional information about
joint phase choices across depths, another probability construction, or
a different sufficient estimate. Keeping the root joint table alone
does not supply that missing relation. No literature-originality claim.
