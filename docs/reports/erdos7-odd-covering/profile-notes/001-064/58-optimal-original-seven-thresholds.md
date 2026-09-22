[Index](../../marked_head_profile.md) · [Allocated source bounds](53-allocated-seven-thresholds-sharpen-actual-survival.md) · [Source refinement boundary](55-an-actual-test-limits-source-refinements.md)

# Exact optimal original-seven thresholds at the off-diagonal endpoint

Fix the profile53 source envelope F at theta404 and full carrier(0,1).
Over all real threshold allocations, including unequal positive-block
thresholds, the complete sums of block envelopes have exact minima

    min C4 = 559961/2572500,
    min C5 = 67605959/405168750.

This optimizes a specified source comparison, not the actual source
integral. The proof uses a global lower functional obtained by selecting
one branch in each envelope maximum. It does not require convexity of
the full comparison in the threshold variables. No new global K bound
or resolution of unrestricted Erdos #7 follows.

## 1. The real-parameter problem

Use the raw source data and five cells of profiles50--55:

    d=(3/4,3/4,1/4,1/2,1/2),
    n=(1/24,1/12,1/36,1/24,1/18),
    eta=(1/18,1/9,1/9,1/9,1/9), omega=(1/5,2/5,0,0,0).

Write h_t(v)=(v-t)_+, chi_t(v)=min(1,h_t(v)), and let p_j be the
complete seven-count law p_1=29/35, p_j=36/(5*7^j) for j>=2.
For each n=2,...,t-1 choose a real vector a_n of length n with

    a_(n,e)>=1, sum_(e<n)a_(n,e)=t.                (1)

Each coordinate belongs to one original seven block e. The underlying
residues of that block remain fixed across all auxiliary outcomes.
Let

    psi_e(v)=sum_(n>e)(p_n/n)*[h_t(n*v)-h_t(n)],
    f_e,l(v)=psi_e(v)-1_(e=0)*omega_l*chi_t(v)
       +sum_(e<n<t,n>=2)p_n*[h_(a_(n,e))(v)-h_(t/n)(v)],
    C_t(a)=sum_(e>=0)F(f_e).                     (2)

The constant s*E h_t(N), present in the full survival source bound,
is independent of a and is not included in C_t. Adding it leaves the
minimizers unchanged. Formula(2) retains every original-seven block.

One minimizing allocation for each threshold is

    t=4: a2=(2,2), a3=(1,3/2,3/2);
    t=5: a2=(2,3), a3=(1,2,2), a4=(1,1,5/3,4/3). (3)

The block values at these allocations are

| t | e=0 | e=1 | e=2 | e=3 | all e>=t-1 |
| --- | --- | --- | --- | --- | --- |
| 4 | 55073/367500 | 381/6860 | 351/34300 | included in tail | 1/490 |
| 5 | 1998757/16537500 | 6227/171500 | 941/120050 | 187/120050 | 1/3430 |

For t=5 this lowers the profile53 root0 allocation's C5 by 2/60025.
The reduction is for this endpoint's fixed source expression and
has not been propagated as a uniform improvement on all parameters.

## 2. A global lower functional from fixed branches

The operator F in profiles31 and53 is a sum of maxima of linear
functionals of the five integer cost sequences. Its first maximum
chooses a ternary shallow baseline b and a deep cell j. At each outer
five-count m there is another maximum for the pure3 cost

    q_m,l(v)=[f_l(m*v)-f_l(m)]/m.

Its positive coefficient is p5_m*(m-1), with p5_m=4/5^m. Replacing
each maximum by one of its terms gives a lower bound for every cost
sequence, irrespective of the signs in the selected linear functional.

Baseline indices below use the existing order

    b(r,j)_l=1+1_(ROOT(l)=r)+1_(l=j), index=5*r+j,
    ROOT=(0,0,1,1,1).

The four baselines used here are

    b1=(2,3,1,1,1), b6=(1,2,2,2,2),
    b7=(1,1,3,2,2), b9=(1,1,2,2,3).

Select the following pairs (baseline index,deep cell):

| t | original block | first source branch | pure3 branch at outer five count m |
| --- | --- | --- | --- |
| 4 | e=0 | (9,4) | (7,2), 2<=m<=4 |
| 4 | e=1,2 | (1,0) | (6,0), 2<=m<=4 |
| 5 | e=0 | (9,4) | (7,2), 2<=m<=5 |
| 5 | e=1 | (9,4) | (7,2) at m=2; (6,0) at m=3,4,5 |
| 5 | e=2,3 | (1,0) | (6,0), 2<=m<=5 |

Retain the complete affine tails exactly. Call the resulting sum
L_t(a). Then

    L_t(a)<=C_t(a) for every feasible real array. (4)

Fixed-branch linearity in f makes L_t separable in the individual
thresholds. The entries of f are evaluated at integer loads, so each
coordinate dependence is affine on every interval [k,k+1]. Its slope
on such an interval is -p_n*E_(n,e,k), with the following exact E:

| t,n,e | exposures from k=1 upward |
| --- | --- |
| 4,2,0 | 19/120, 8/75 |
| 4,2,1 | 23/120, 23/150 |
| 4,3,0 | 19/120 |
| 4,3,1 or2 | 23/120 |
| 5,2,0 | 19/120, 8/75, 89/1125 |
| 5,2,1 | 19/120, 8/75, 833/10125 |
| 5,3,0 or1 | 19/120, 8/75 |
| 5,3,2 | 23/120, 23/150 |
| 5,4,0 or1 | 19/120 |
| 5,4,2 or3 | 23/120 |

Only the displayed intervals can occur: (1) implies
a_(n,e)<=t-n+1. Each coordinate's exposures are nonincreasing.
Starting at all thresholds1, the available surplus for fixed n is
t-n. Its optimal allocation selects the largest t-n segment
exposures across the n coordinates. Decreasing exposures ensure
that every selected segment can be preceded by all earlier segments
in its coordinate. If exposures tie, arbitrary splitting among them
gives the same value. This proves the minimum over real allocations,
including fractional segments, rather than just integer arrays.

For t=4,n=2 the first segment in each coordinate is selected. For
n=3 the one surplus unit can be split between e=1 and e=2. For
t=5,n=2 both first segments and one of the tied second segments are
selected; n=3 selects the first e=2 segment and a first segment of
e=0 or1; n=4 selects between e=2 and3. In particular(3) minimizes
L_t in both cases.

Direct evaluation of the finite maxima at(3), with their exact deep
tails, shows that every selected branch is active. Consequently

    min L_t=L_t(a*)=C_t(a*)>=min C_t>=min L_t.     (5)

This proves both stated exact optima. No assumption about a common
maximizing actual test or vanishing outer Jensen loss enters(5).

## 3. Complete tails and exact verification

For e>=t-1 the cost is affine:

    psi_e(v)=6/(5*7^e)*(v-1).

At theta404, F(v-1)=1/2. The entire unchanged seven tail is therefore

    sum_(e>=t-1)F(psi_e)=1/(10*7^(t-2)).           (6)

The outer five-count cost is affine for m>=t+1; its probability and
first moment tails are summed as geometric series. The deep ternary
increments also have a finite affine entrance followed by a complete
geometric series. These facts justify the finite branch and exposure
calculations without truncating any original exponent.

The [checker](../../frontier/comparison-bounds/optimal_seven_thresholds.py) and
[exact data](../../certificates/source_norms/comparison-bounds/optimal_seven_thresholds.json)
reconstruct(3), every entry in the exposure table, the active maxima,
the separable lower minimum and both full tail sums. They bind the
profile53 certificate and its source operators.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/optimal_seven_thresholds.py
```

The ordinary argument supplies the real-parameter quantifier; exact
finite arithmetic checks its premises. There is no Lean claim. The
source-only obstruction of profile55 continues to apply, including
to these optimal threshold allocations. Further unrestricted progress
requires a change beyond this threshold family.
