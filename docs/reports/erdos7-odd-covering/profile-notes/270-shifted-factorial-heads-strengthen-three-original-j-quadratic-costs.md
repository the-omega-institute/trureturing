[Index](../marked_head_profile.md) · [Complete retained source model](256-a-second-seven-depth-sharpens-the-complete-retained-j-heads.md) · [Complete omitted pair bound](265-complete-raw-prime-paths-improve-the-positive-seven-pair-block.md) · [Previous complete comparison](268-three-retained-labels-and-complete-raw-paths-improve-the-full-j-comparison.md)

# Shifted factorial heads strengthen three original J quadratic costs

On both entire actual saturated J faces, the following uniform bounds
hold for the unchanged original cost functions and every admissible
complete load A:

| Original cost index | Complete exact upper | Decimal prefix |
| --- | ---: | ---: |
|41|5245754677795648762319929/1044555982470000000000000|5.021994766993073638664188...|
|47|17598958580280095317/5556600000000000000|3.167217107634181930856998...|
|48|12209082857318579/3240000000000000|3.768235449789684876543209...|

Their improvements over the corresponding adopted original-cost bounds
in268 are respectively

    0.046337675626853692197905...,
    0.120018558061680741100673...,
    0.106180398031107667458517... .                         (SF1)

Each target keeps all62,500,000 original containing choices, the whole
late interval, all retained135/125 membership states, independent
147/245 projections and every omitted prime/cofactor depth. The common
source model has3306 variables,6354 inequalities and18 equalities.
These are three complete cost inequalities; a full52-cost comparison
requires a separate consumer.

## Exact shifted expansions of the original functions

For integer n>=1 write

    H_t(n)=(n-t)_+,
    Phi4(n)=(n-4)_+*(n-3)_+/2,
    Phi5(n)=(n-5)_+*(n-4)_+/2.

The identity Phi4=Phi5+H4 gives the following exact expansions:

    cost41(n) = (75376570/184225041)*H1(n)
              + (474292550/184225041)*H2(n)
              + (512/429)*H3(n) + (2212/429)*H4(n)
              + (8/3)*Phi4(n),

    cost47(n) = (11/4)*H4(n)+(17/4)*H5(n)+2*Phi4(n),

    cost48(n) = 7*H3(n)+2*Phi4(n).                         (SF2)

All retained hinge coefficients are nonnegative. Costs47 and48 are the
original positive parts of n^2-81/4 and n^2-9. Cost41 has the unchanged
quadratic continuation(4/3)*n^2-2535551750/184225041 from n=4.

The checker verifies every finite transition and all three coefficients
of each entire polynomial continuation. For an expansion

    a + sum_t c_t*H_t(n) + f*Phi4(n),

those coefficients are

    quadratic: f/2,
    linear: sum_t c_t-7*f/2,
    constant: a-sum_t t*c_t+6*f.                          (SF3)

Thus(SF2) holds at every positive integer load; no numerical load cutoff
is used. The change of basis alone supplies no improvement. The bounds
below keep the shifted head and the positive hinge part on the same
actual source, instead of separately optimizing their scalar moments.

## One original head controls the complete factorial remainder

Use the original six-label old head

    B=1+I3+I9+I5+I15+I45,    1<=B<=6,

and decompose the full load as A=B+T, where T=O+Z contains every omitted
old label and every positive-seven label. Put h=(B-3)_+. Then

    Phi4(B+T) <= Phi4(B)+h*T+binom(T,2)                  (SF4)

for every nonnegative integer T. If B>=3, the two sides are the same
quadratic polynomial in T. If B=1 or2, Phi4(B)=h=0 and

    Phi4(B+T)=binom((B+T-3)_+,2)<=binom(T,2),

because0<=(B+T-3)_+<=T and binom(v,2) is nondecreasing on nonnegative
integers. These six head cases cover every possible original head.

For a fixed original layout and the actual common late parameter theta,
the complete cross in(SF4) is bounded by

    C_B(theta)=OldTail(w*h)+RawRow(h,theta)/5.             (SF5)

OldTail is241's complete old-label operator, with all pure and mixed
3/5 depths. RawRow takes the sum of the maxima over all six independent
raw-head cofactor mask families and adds OldTail(h). These mask-family
sizes are1,2,5,5,10,25. Every full cofactor test is therefore retained.
The positive-seven factor1/5 is the complete all-depth sum supplied by
the original source bridge. Its raw term uses Lambda, of mass1/4;
it does not insert the survivor density w. The old-label term uses w*h.

The head h is used exactly. It is not replaced by a coarse45/intersection
mask. For fixed nonnegative coefficients the raw cap expression is affine
in theta, and OldTail has no theta dependence. Each maximum over a mask
family is convex in theta, so C_B is convex. Writing

    theta=LO+(HI-LO)*x,    0<=x<=1,
    LO=1/135, HI=1/90,

therefore gives the valid common-coordinate secant

    C_B(theta)<=(1-x)*C_B(LO)+x*C_B(HI).                 (SF6)

The same x is used in every source row and objective. There is no
independent optimization of different late parameters.

The complete distinct-pair term of(SF4) uses265's bound

    integral binom(T,2)dmu <=4879/7200.                  (SF7)

Its complete ordered tail square is5737/3600, and its old and positive
seven diagonals are53/600 and3/20. The exact consistency identity is

    4879/7200 = (5737/3600-53/600-3/20)/2.

All three terms are bounds on the assigned cap series in the complete
pair expansion; this is not subtraction of an unknown diagonal from an
unknown actual moment. No selected label or exponent tail is discarded.

## The retained joint objective and every pruning line include the full cost

Keep256's entire actual source polytope, including raw cells, survivor
cells Y, marked deletions, retained135/125 states and their complement.
The positive hinge part of(SF2) uses256's two-depth seven objective, with
complete positive-seven remainder37/1225. This still retains all
21,35,63,105,147,245 projections and complete zero-seven tails.

For a cost a+sum c_t H_t+f Phi4, add

    f*sum_(cell,mask) Y_(cell,mask)*Phi4(B_cell)

inside that same LP. Add f*(C_B(HI)-C_B(LO)) to its normalized common-x
column875, and add the outside constant

    f*(C_B(LO)+4879/7200)+a*(3/20).                       (SF8)

This is(SF4)--(SF7) coupled to the actual hinge source. Column875 can
have either sign; every other objective coefficient is nonnegative.
The rational dual checker permits this signed objective and checks all
3306 domination columns. Inequality multipliers remain nonnegative;
equality multipliers remain unrestricted.

Every two-, four- and six-projection affine pruning bound also includes
the full shifted-factorial head, cross secant, complete pair term and
constant a*(3/20). The affine factorial head is the raw source bound on
w*Phi4(B) minus the full original deletion correction. Its two endpoints
and(SF6) give a valid affine upper throughout the same late interval.
Taking the minimum of the complete affine lines and the complete joint
dual therefore preserves the full cost. A hinge-only251 certificate is
never used to prune a full quadratic cost.

The positive hinge and factorial bounds each control their own addend
in the exact identity(SF2). Their complete tails are both retained; no
saving is counted twice and no common-source attainment is assumed.

## Complete coverage, exact duals and scope

For each target the search covers12,500 independent old-head layouts,
10 choices for21/35,50 for63/105 and10 for147/245. If n2 and n4 are
numbers pruned at the first two stages and n6 is the number reaching
the last stage, the exact accounting law is

    500*n2+10*n4+n6=62,500,000.                            (SF9)

The certificate retains the complete counts:

| Cost | First-stage prunes n2 | Second-stage prunes n4 | Last-stage branches n6 | Joint-dual branches |
| --- | ---: | ---: | ---: | ---: |
|41|124989|466|840|541|
|47|124992|387|130|65|
|48|124991|415|350|288|

There are895 distinct exact duals, including seeds, and2,958,870 rational
column checks. The complete three-target inventory is187,500,000 choices.
Before any pruning, the checker reconstructs all12,500 factorial-head
components at both endpoints and hashes all25,000 endpoint records.
It also verifies the independently written unscaled affine formulas,
all exact original-cost expansions, the whole source closure and every
branch-decision digest.

For all three targets the maximizing certificate branch is

    layout=(1,4,2,1,2,4,2),
    projections21/35/63/105/147/245=(1,4,4,1,4,1,4).

The common affine maximizer is x=1; the adopted bound uses the full joint
dual. This identifies a maximizing bound calculation, not a claim that
one actual covering family attains all source caps.

The [checker](../frontier/j_face_shifted_factorial_quadratic_heads.py)
and [certificate](../certificates/source_norms/j_face_shifted_factorial_quadratic_heads.json)
use Python standard-library rational arithmetic. The retained dual bank
contains exactly the duals used by the three complete scans; canonical
replay reconstructs the entire certificate.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j_face_shifted_factorial_quadratic_heads.py --check
```

These inequalities apply on both entire saturated actual J faces. They
do not supply a full52-cost ratio, a crossing of403, an off-face
extension, a global join, Lean verification or unrestricted Erdos7.
