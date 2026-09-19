[Index](../marked_head_profile.md) · [Joint pure-three moment](171-the-pure-three-path-has-a-joint-complete-moment-bound.md) · [Complete projected defects](125-the-complete-off-face-omitted-tails-recover-every-face-constant.md) · [Independent shallow transport](152-independent-shallow-indicators-sharpen-the-complete-mean-and-square.md) · [Pure-five shared error](165-the-pure-five-joint-envelope-enters-both-complete-comparisons.md)

# The pure-three joint moment transports one actual residual

The all-depth pure-three bound now holds on four existing complete
source rectangles with one actual defect budget. Replacing its
single category in the full square gives these complete comparisons:

|Input|Source radius delta|Residual radius R|Previous complete K|New complete K|Full-square saving|
|---|---:|---:|---:|---:|---:|
|176|1/26|1/940|509.030886991151|508.923226784244|0.060587945254|
|178|1/25|1/1000|501.856905315781|501.749180464249|0.061232126042|
|181|1/20|1/1000|505.701239618792|505.584837754314|0.065898479406|
|170|1/18|1/13000|506.975514690183|506.838749547857|0.077277200767|

Each domain includes its complete actual slot-loss range r<=5R.
All52 original independent costs, the existing pure-five gain,
the full denominator and every infinite tail remain. These are
ordinary actual-source theorems with exact rational consumers.
They do not change a global bound or resolve unrestricted Erdos7,
and are not Lean or frozen results.

## 1. One cellwise reference and one projected excess

Write delta for a source-radius bound and rho for the actual
nonnegative residual; rho<=R. Use125's actual survivor projection
mu3, raw ternary measure eta and canonical cells
ROOT=(0,0,1,1,1). The concentration inequalities of134 imply

    d0,d1<=3/4+delta/4,
    d_l<=1/2+delta/2-beta_l for l>=2,
    a0<=1, a_l<=4/5+delta/5 for l!=0.               (JT1)

Here beta_l>=0. These geometric inequalities follow from the
source concentration and the same carrier mass pi_(1,1)>=1-delta;
they do not require the old positive-r wrapper. The four inputs
re-establish their own complete first-label and packing guards.
Set

    C0=7/10+delta/4,
    C1=11/20+7delta/20+delta^2/20,
    C2=C3=C4=3/10+delta/2+delta^2/10,
    Dbar=3/4+delta/4, H=Dbar-min_l C_l.             (JT2)

Thus each C_l bounds a_l*d_l-(1+ROOT(l))/20 from above.
By125(OT3), with C denoting the piecewise constant reference,

    nu=(mu3-C*eta)_+,
    nu(1)<=E5+E5deep+kappa*(E15+E15deep)+omega,
    nu|cell_l<=(Dbar-C_l)*eta|cell_l<=H*eta|cell_l. (JT3)

Increasing the reference to C only decreases its positive excess.
The raw bound mu3<=Dbar*eta proves the second line's density
envelope. This is a single positive measure for every pure-three
test, including tests whose cells change at every depth.

Use152's actual shifted defects with the original packing gap g:

    z=(E5-g*q5, E15-g*q15, E27, Ege4,
       E5deep, E15deep, omega, g*q5, g*q15)>=0,
    sum z_i<=rho<=R.                              (JT4)

In particular E27+Ege4=E3, not a second budget. Also
kappa<=kbar=(6-delta)/(3-2delta). Consequently

    nu(1)<=w.z,
    w=(1,kbar,0,0,1,kbar,1,1,kbar).                (JT5)

All four denominators and all first-label gaps are positive on
the inherited domains. The source-radius inequalities are uniform
over every allowed beta vector. First-beta cases L=2,3,4 are kept
separately. The other K orientation applies the original root0-cell
exchange simultaneously to the source, indicator rows and C.

## 2. Keep both shallow choices before sharing the error

For each first-beta case,152's exact original indicator rows give

    mu(J1(root r))<=A_r+p_r.z,
    mu(J2(cell j))<=B_j+p_j.z.                    (JT6)

Their zero-residual terms are reconstructed as

    finite_transport.finite_upper-reference
                              +source_delta_price*delta.

The first seven prices are the stored coordinate_prices; both last
prices are q_sum_price/g. The helper checks each complete row
against the pinned original rectangle. It never uses the already
separately maximized upper as a zero-residual source term.

Let Z=sum_(a>=1)1_(J_a), with independent original labels J_a.
Fix r,j and put n_l=I(ROOT(l)=r)+I(l=j). The shallow contribution
to integral(Z^2+2Z) is at most

    3*A_r+(3+2*I(ROOT(j)=r))*B_j+P_rj.z,
    P_rj=3*p_r+(3+2*I(ROOT(j)=r))*p_j.             (JT7)

For the reference part of all a>=3,171's Bellman argument applies
to any nonnegative cell caps C_l. Its potential at count n is

    V_l(n)=C_l*((2*n_l+3)/(1-1/3)
                                  +(2/3)/(1-1/3)^2).

The same-cell recurrence is exact. Other potentials are unchanged
and the one-step reward is at most(1-1/3)*V_l(n). The maximum
potential therefore bounds arbitrary choices at all later depths.
After multiplying by3^-3, the complete reference tail is

    max_l C_l*(n_l+2)/9.                          (JT8)

No nesting of the independently labelled cylinders is imposed.
Replacing actual compatibility by agreement of their depth-two
cell only enlarges the reference bound.

## 3. An exact infinite error tail and a finite residual maximum

The term whose deepest exponent is a has multiplicity at most
2a+1 in Z^2+2Z. The same nu from(JT3) therefore contributes at most

    G(e,H)=sum_(a>=3)(2a+1)*min(e,H*3^-a), e=w.z. (JT9)

For e>0 let N>=3 be the first exponent with H*3^-N<=e. Then

    G(e,H)=(N^2-9)*e+H*(N+1)/3^(N-1),
    G(0,H)=0.                                    (JT10)

The geometric term contains the entire infinite tail. The bound
for a fixed r,j is thus

    3*A_r+(3+2*I(ROOT(j)=r))*B_j
       +max_l C_l*(n_l+2)/9
       +max_(z>=0,sum z<=R)[P_rj.z+G(w.z,H)].     (JT11)

The maximum in(JT11) is finite-dimensional and exactly computable.
The three residual weight classes are0,1,kbar. For P=P_rj define

    p0=max(0,P_2,P_3),
    p1=max(P_0,P_4,P_6,P_7),
    pk=max(P_1,P_5,P_8).                          (JT12)

The classes are{2,3},{0,4,6,7},{1,5,8}; capital P_i denotes an
original coordinate price and lowercase p denotes a class maximum.
Including unused budget as a zero-price weight-zero coordinate,
the maximum shallow price at fixed e is the upper boundary of

    R*conv{(0,p0),(1,p1),(kbar,pk)}.               (JT13)

The helper checks all three segments joining these vertices.
This includes that upper boundary; every point of every checked
segment is itself a feasible two-class residual allocation.
On a segment, the objective is piecewise linear, with possible
corners only at its endpoints and e=H*3^-n.

The geometric corners accumulate at zero but require only finitely
many checks. If s is a segment's slope and its left endpoint is
zero, choose n with H*3^-n inside the segment and n^2-9+s>=0.
On every omitted smaller interval the slope of G is at least
n^2-9. Their total objective is therefore nondecreasing toward
the retained corner. A segment with positive left endpoint has
only finitely many geometric corners to begin with. This proves
the exact finite stopping rule used by the rational consumer.

Finally maximize(JT11) over all30 first-beta/root/cell choices.
At delta=R=0 this recovers34/45 exactly. For the four positive
rectangles, all three first-beta choices maximize at r=0,j=1.
No claim is made that an actual family realizes these relaxed
equalities or that all separately bounded quantities saturate
simultaneously.

For fixed actual sources, monotone convergence justifies the moment
expansion. For varying finite sources, the raw bound
mu(J_a)<=3^-a gives the uniform missing-depth bound
sum_(a>A)(2a+1)*3^-a, tending to zero. Stabilizing finitely many
labels at each finite depth preserves the same source-limit scope
as171; no tail is inferred from a finite height sample.

## 4. Substitute one disjoint category into the complete comparison

In the original LCM square, the pure-three category consists of
all ordered pairs with five and seven exponents zero, excluding
the unit-unit pair. Its multiplicities are2a+1; hence it is exactly
Z^2+2Z. It is disjoint from the already improved pure-five category,
the mixed categories and all positive-seven terms.

At delta=1/26,R=1/940 the new category is

    3552162031/4101924060=0.865974596077724559...,

and its improvement over176's complete original category is

    9976873925021/164667639464640
       =0.060587945254194220... .                 (JT14)

For every rectangle, write DeltaQ for its positive category saving,
cQ for the original positive full-square weight, and N,D,M,b for
the previous signed numerator, complete denominator, actual-mass
coefficient and target offset. The exact consumer computes

    N_new=N-cQ*DeltaQ,
    K_new=b+N_new/D.                              (JT15)

It reconstructs N from all original cost groups plus the original
signed mass term, checks every actual cost index0..51 occurs once,
and reconstructs D from the complete denominator objectives and
H1. Only the square group's constant changes. The coefficient of
the actual mass is unchanged, and

    (K_new-b)*(1-1/614922)-M>0

holds in all four cases. Thus(JT15) is a complete comparison on
each whole original rectangle, not just at its mass floor.
For176 the exact resulting bound is

    K<=445286819128215970896193072740682747163178294124877319210671
         /874958727943837955380863364680061712084888772294192000000
      =508.923226784244547665755507... .

The [helper](../frontier/pure_three_joint_source_comparison.py) and
[certificate](../certificates/source_norms/pure_three_joint_source_comparison.json)
retain all inherited input closures, all shallow rows, all residual
segments and their exact tail crossings. The complete comparisons
remain above403. New source domains or a new global join require
their own complete proof; neither follows from these local savings.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/pure_three_joint_source_comparison.py --check
```
