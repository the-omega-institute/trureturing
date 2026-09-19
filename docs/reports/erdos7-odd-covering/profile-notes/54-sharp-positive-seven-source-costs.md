[Index](../marked_head_profile.md) · [Actual source endpoints](50-sharp-source-survival-endpoints.md) · [Two-baseline source correction](51-sharp-off-diagonal-source-costs.md)

# Sharp positive-seven source costs at the off-diagonal endpoint

At theta404 the first positive-seven block of the threshold5 source
comparison has sharp limiting supremum

    108369/2401000,

strictly below its inherited envelope110031/2401000 by

    delta5=831/1200500.

Every other positive-seven block at thresholds4 and5 has its old
source bound attained. All these block extrema can be approached on
the same actual off-diagonal forbidden source families of profile50,
with separately assigned original residues for each original7 block.
These are sharp scalar35 source costs. They do not assert sharpness
of the full357 hinge or absorbed deletion comparison.

The proof is ordinary mathematics with exact rational premises.
No Lean verification or global K improvement is claimed.

## 1. Costs, endpoint and the complete values

Put

    h_t(v)=(v-t)_+,
    p7_1=29/35, p7_n=36/(5*7^n) for n>=2,
    c_(t,e)(v)=sum_(n>e)(p7_n/n)*[h_t(nv)-h_t(n)], e>=1.

Let F_theta be the complete common35 source envelope of profile31.
The raw source Lambda, its ternary marginal lambda and pure3 measure
eta are exactly those of profiles50 and51. At theta404,

    d=(3/4,3/4,1/4,1/2,1/2),
    n=(1/24,1/12,1/36,1/24,1/18),
    eta=(1/18,1/9,1/9,1/9,1/9), s=1/4, D=3/20.

The five cells are C0=[0]9,C1=[3]9,C2=[1]9,C3=[4]9,C4=[7]9.
The ten shallow ternary baselines are

    b_l=1+1_(ROOT(l)=r)+1_(l=j), ROOT=(0,0,1,1,1),

ordered by r=0,1 and then j=0,...,4. The two used below are

    b+=(2,3,1,1,1), index1;
    b-=(1,1,2,2,3), index9.

The complete values are:

| Cost | Old F_theta404 | Sharp limiting supremum | Actual test |
| --- | --- | --- | --- |
| c_(4,1) | 482/8575 | 482/8575 | W^(+,-) |
| c_(4,2) | 187/17150 | 187/17150 | W^(+,-) |
| c_(5,1) | 110031/2401000 | 108369/2401000 | W^- |
| c_(5,2) | 4523/480200 | 4523/480200 | W^(+,-) |
| c_(5,3) | 771/480200 | 771/480200 | W^(+,-) |

For e>=t-1 the whole cost is already affine on v>=1:

    c_(t,e)(v)=6/(5*7^e)*(v-1).

Its sharp value is3/(5*7^e), attained by W^(+,-). Consequently the
sharp sums of positive block costs, with all exponent tails, are

    B4=593/8575,
    B5=135539/2401000.

The affine block tails are1/490 for t=4,e>=3 and1/3430 for t=5,e>=4.
Here B_t denotes only sum_(e>=1) F(c_(t,e)). The existing full positive7
complement also includes the unchanged constant s*E[h_t(N)], where

    E[h_t(N)]=1/(5*7^(t-1)).

Thus replacing that full complement by its sharp block version saves
exactly delta5 at theta404 for t=5, and zero for t=4. This is a correction
at this source endpoint; delta5 is not asserted as a uniform constant
over the whole continuous parameter domain.

## 2. A source correction valid on the general parameter domain

The scalar case of profile51 already supplies the required universal
inequality. For completeness, let f be nonnegative increasing convex
on[1,infinity), with affine tail f(v)=A*v+B above an integer K>=2.
Retain profile31's actual source hypotheses, including

    0<=d lambda/d eta<=d_l, d_l>=1/4.

Write p5_m=4/5^m for m>=2 and define

    q_m(v)=[f(mv)-f(m)]/m,
    bar_f(v)=sum_(m>=2)p5_m*q_m(v)-f(v)/5,
    D_f(a)=sum_(k>=0)3^(-k-3)*[f(a+k+1)-f(a+k)],
    P_eta(q;b)=sum_l eta_l*q(b_l)+max_l D_q(b_l),
    Z_f(b)=sum_l[n_l*f(b_l)+eta_l*bar_f(b_l)]
                 +max_l[d_l*D_f(b_l)+D_(bar_f)(b_l)].

The last expression is valid because
d_l*f+bar_f=(d_l-1/5)*f+sum_m p5_m*q_m is increasing convex.
For the same two original ternary test blocks A0,A1, with shallow
baselines b,c, put

    J_f(u,v)=[f(2u)+f(2v)]/2-f(u+v),
    L_f(b,c)=sum_l eta_l*J_f(b_l,c_l)-max_l J_f(b_l,c_l)/9.

The union of their deep ternary cylinders has eta mass at most1/9.
Off this union the loads equal b_l,c_l. Since J_f is nonnegative,

    integral_eta J_f(A0,A1)>=L_f(b,c).

For m=2 retain this exact Jensen defect. For every other m use the
original Jensen inequality, retaining the same original A1 through
all its appearances. Define

    R_f(c)=sum_(m>=2)p5_m*[eta(1)*f(m)+P_eta(q_m;c)
                                  +(m-2)*max_a P_eta(q_m;a)].

Then every finite independently labelled original35 test Z satisfies

    integral_Lambda f(Z)<=F_f^J(theta),
    F_f^J(theta)=max_(b,c)[Z_f(b)+R_f(c)-(4/25)*L_f(b,c)].       (1)

This is precisely profile51's scalar correction. No new source,
auxiliary choice of residues, or repeated deletion payment enters it.
One can also replace L_f by its positive part for a valid bound;
formula(1) deliberately leaves it untruncated. For each fixed b,c,
the correction is affine in eta, preserving profile51's separate
convexity argument. The positive-part variant needs its own parameter
argument and is not used for that claim here.

All sums are complete. With T0=sum_(m>=K)p5_m and
T1=sum_(m>=K)m*p5_m, the exact tail of R_f(c) is

    eta(1)*(A*T1+B*T0)
      +A*T0*P_eta(v-1;c)+A*(T1-2*T0)*max_a P_eta(v-1;a).

Each deep sum has an exact affine geometric tail. Hence(1) is a finite
maximum of continuous expressions for fixed f. Its value at theta404
bounds every approaching family's limsup, not only the explicit
construction used for the matching lower value.

## 3. The exceptional first positive block at threshold5

For f=c_(5,1), complete evaluation of the7 series gives

    f(1)=0, f(2)=117/12005,
    f(v)=(6/35)*v-4881/12005 for v>=3.

For integers u,v>=1 the Jensen defect is therefore

    J_f(u,v)=9/245 if exactly one of u,v equals1,
             0 otherwise.                              (2)

All m>=3 positive5 costs are affine, so only the m=2 Jensen step
can lose information. Evaluating all100 pairs in(1) gives the following
ten values after maximizing c. To keep the table integral, subtract
the common positive-block affine constant2424/300125 and multiply
by7203000:

| Zero baseline index | Scaled maximum using L_f |
| --- | --- |
| 0 | 220173 |
| 1 | 255453 |
| 2 | 201943 |
| 3 | 202918 |
| 4 | 203893 |
| 5 | 238206 |
| 6 | 249367 |
| 7 | 241451 |
| 8 | 257131 |
| 9 | 266931 |

The table with max(0,L_f) differs only at index5, giving235854.
Both maxima are266931. Since7203000*(2424/300125)=58176,

    F_f^J(theta404)=(266931+58176)/7203000
                   =108369/2401000.                    (3)

The maximizing zero baseline is9; a positive baseline can be7,8,9.
For the actual test below choose9 for both. By(2), its actual Jensen
defect vanishes because A0=A1. Its deep cylinders also attain the
chosen source and pure deep costs. The value in(3) is therefore sharp.

For the other four finite costs in the opening table, f is affine on
the integer arguments v>=2. Every positive5 Jensen step then has all
its arguments in that affine region and is equality. Their old
zero5 maximizing baseline is1, while positive blocks can use9. The
actual W^(+,-) below realizes both choices at once.

## 4. Actual original35 tests and their complete integrals

Use the off-diagonal forbidden families of profile50, at finite height
N, on all their original labels. In the limiting notation define

    T^-(x)=1+sum_(a>=1)1_[7]_(3^a)(x),
    T^+(x)=1+1_[0]_3(x)+sum_(a>=2)1_[3]_(3^a)(x),
    H_b(y)=1_[4]_(5^b)(y),
    W^-=T^-*(1+sum_(b>=1)H_b),
    W^(+,-)=T^++sum_(b>=1)H_b*T^-.

All finite truncations assign exactly one residue to each original
3^a5^b test label. For W^(+,-), the b=0 block has the T^+ residues;
every b>=1 block has the T^- residues. This is allowed by the original
labelled test model; it does not change a block's residues across
auxiliary outcomes.

The T^+ deep chain is in C1, the T^- chain in C4. Those chains meet
no pure3 or late35 forbidden cylinders. In the limit the respective
lambda-to-eta densities are d1=3/4 and d4=1/2. Every H_b lies in the
source-free first5 class[4]5. Consequently, for either chosen zero
block A0, its actual integral is exactly

    I_f=integral_lambda f(A0)
       +sum_(b>=1)5^-b*integral_eta[
           f(A0+b*T^-)-f(A0+(b-1)*T^-)].              (4)

The zero-block term is

    sum_l n_l*f(b_l)+d_j*D_f(3),

where(b,j)=(b-,4) or(b+,1). For W^-, the pure integral of
f(A0+k*T^-) is

    sum_l eta_l*f((k+1)*b-_l)
      +sum_(i>=0)3^(-i-3)*[
          f((k+1)*(4+i))-f((k+1)*(3+i))].

For W^(+,-), put a_l=b+_l+k*b-_l. Its pure integral is

    sum_l eta_l*f(a_l)
      +sum_(i>=0)3^(-i-3)*[f(a_1+i+1)-f(a_1+i)]
      +sum_(i>=0)3^(-i-3)*[f(a_4+(i+1)*k)-f(a_4+i*k)].

The two deep terms have disjoint ternary supports. These formulas,
with exact affine tails, evaluate(4) to the opening table. Every tail
uses the actual slope of f, namely6/(5*7^e); it is not replaced by1.
They also give F_theta404(v-1)=I_(v-1)(W^(+,-))=1/2.

For finite heights, the same formulas truncate the actual deep and5
sums, using the finite source parameters of profile51. Direct forbidden
source masks at heights3 and4 give28 matching finite integral values
across the two tests and seven finite/affine-entrance costs.

The forbidden sources decrease and these tests increase with height.
Both complete tests have full Haar mean15/8. Since
0<=c_(t,e)(v)<=6/(5*7^e)*(v-1), dominated convergence proves every
claimed actual limit. The same estimate and the geometric e tail
justify summing all positive blocks. Formula(1), its continuity, and
the complete affine tail prove the matching universal upper limits.

## 5. The original7 cylinders realize the comparator law in the limit

The same off-diagonal forbidden family uses

    G_(j,e)=[j*7^(e-1)]_(7^e),

with class6 for pure7 and classes1,2,3,5 for mixed7. Choose the
original7 test cylinders

    K_e=[4]_(7^e), e>=1.

They are nested and disjoint from every forbidden seven cylinder:
their first7 digit is4, while a G cylinder has first digit j for
depth1 and0 at every deeper depth. Thus there is no7-carrier loss on
any K_e for these forbidden families.

At finite height N the normalized pure7 survivor law has denominator

    u_N=1-sum_(e=1..N)7^-e=(5+7^-N)/6.

For e<=N its K_e probability is7^-e/u_N, not yet6/(5*7^e).
Writing M_N=1+sum_(e=1..N)1_(K_e), the exact probabilities are

    Pr(M_N=1)=1-7^-1/u_N,
    Pr(M_N=m)=(7^(-(m-1))-7^-m)/u_N, 2<=m<=N,
    Pr(M_N=N+1)=7^-N/u_N.

As N tends to infinity these converge to p7. The last finite atom
retains the complete count tail. This statement is about the normalized
pure7 law before mixed357 deletion. It does not identify p7 with the
law after conditioning on the full357 survivor.

For each original3^a5^b7^e test label, take the CRT product of the
selected old35 block residue and4 modulo7^e. Distinct exponent triples
give distinct moduli; every label receives one genuine residue. For
t=4, use W^(+,-) in every e>=1 block. For t=5, use W^- at e=1 and
W^(+,-) at every e>=2. A zero block W^- can be chosen independently
at e=0, as in profile51's absorbed extremizers. Hence the blockwise
choices coexist on the same actual source family, which still has
S_N tending to3/20 and shallow carrier tending to(0,1).

## 6. What this leaves open in the full357 comparison

With the nested K_e and fixed original blocks A_e, the remaining
pre-deletion outer Jensen defect is exactly

    integral_Lambda sum_(m>=1)p7_m*[
       (1/m)*sum_(e=0..m-1)h_t(m*A_e)
          -h_t(sum_(e=0..m-1)A_e)].                   (5)

Every A_e>=1. For m>=t all hinge arguments are in the affine region,
so the bracket is zero. The only possibly nonzero terms are m=2,3
for t=4 and m=2,3,4 for t=5. The residue compatibility inside this
finite outer front is still a separate question. Deletion clipping
is also a distinct step. Attaining all scalar source block bounds
does not prove that(5) or the clipping loss vanishes.

At theta404, using the corrected positive complement in the inherited
absorbed threshold5 inequality with unallocated original hinges improves that endpoint's margin by
delta5. With its inherited4/33 coefficient the corresponding combined
endpoint gain is277/3301375. This is not a global numerical K result.
For other parameters the legitimate correction is the function in(1),
possibly combined with the old upper bound; the endpoint constant
cannot simply be subtracted everywhere.
If another comparison has already changed the positive block costs
through threshold allocation, this delta5 cannot automatically be
subtracted from those changed costs a second time.

## Verification

The standard-library checker
[positive_seven_source_extrema.py](../frontier/positive_seven_source_extrema.py)
reconstructs500 baseline pairs, five exact sharp finite block values,
the complete affine tails and the existing positive7 constants. Its
independent direct-integral formulas retain each cost's own affine
slope. It also checks28 finite original35 integrals, three finite
pure7 count laws, and four original357 test label families.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/positive_seven_source_extrema.py
```

The checker is read-only by default, with optional `--output PATH`.
`--base REPORT_ROOT` selects the canonical dependency root when run
from staging. Only pinned canonical helpers are loaded. Finite exact
checks verify the displayed premises; the ordinary arguments above
supply universal inequalities and the infinite limits.
