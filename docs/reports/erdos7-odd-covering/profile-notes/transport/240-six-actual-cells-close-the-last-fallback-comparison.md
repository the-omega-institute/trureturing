[Index](../../marked_head_profile.md) · [Previous fallback](236-the-last-missing9-branch-uses-a-better-ap-threshold.md) · [Unequal source norms](../32-unequal-source-norms-sharpen-the-uniform357-input.md) · [Signed deletion](../../problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md)

# Six actual cells close the last fallback comparison

When the forbidden modulus3 is present and the forbidden pure9 is absent or
ineffective, the complete actual uniform357 source satisfies

    square <=13591/468=29.04059829059829...,
    ambient survivor mass >=19/108,
    normalized Haar density <=108/19.

For the final fallback, where forbidden5 and7 are both present, these bounds
on the same actual source give the complete physical AP(4,4) comparison

    K <=11331588321088832533976833424812498436492429
        /29713258622641625220302292173698103400000
       =381.36471213070234 <403.

The two recomputed complete finite-core errors are0.0004733590579004415 and
0.1808968036007922. Their remaining margins below403 are21.63481451023976
and21.454391065696868. The first seven fallback records retain236's separate
AP(4,5) laws and bounds; all eight complete fallback comparisons are below403.
The effective9 domains and the unrestricted continuation are separate.

## Six cells extracted from the actual family

Extend the finite ambient period to include9 if needed, without adding a
forbidden class. The two roots outside the forbidden mod3 root contain six
mod9 cells, with root map R=(0,0,0,1,1,1). An ineffective forbidden9 is already
inside the forbidden mod3 root, so it removes none of these six cells.
Every additional effective pure3 exclusion has exponent at least3. Their
total raw Haar mass is at most sum_(a>=3)3^-a=1/18. Write the actual pure3
mass in cell l as eta_l=w_l/9, with

    w_l=1-delta_l, delta_l>=0, sum delta_l<=1/2.

Let z>=3/4 be the actual pure5 survivor mass. Let alpha_r be the five-coordinate
mass removed from these survivors by the complete3*5^b family in root r.
Let beta_l be the additional mass removed by9*5^b in cell l, after the alpha
deletion. Each family has total five mass at most sum_(b>=1)5^-b=1/4. The
remaining mixed classes, with ternary exponent at least3, remove additional
actual ambient masses t_l whose sum is at most1/72. Independence of the raw
ternary and five coordinates before this last deletion gives exactly

    d_l=z-alpha_R(l)-beta_l,
    n_l=w_l*d_l/9-t_l,
    s=sum_l n_l.

Thus every actual family lies in the product of the delta simplex of budget
1/2, alpha simplex of budget1/4, beta simplex of budget1/4, t simplex of
budget1/72, and z interval[3/4,1]. This containing domain has
7*3*7*7*2=2058 vertices. On the entire domain w>=1/2,d>=1/4,n>=0. The separately
affine mass s has vertex minimum1/3, so s>=1/3 everywhere by successive
simplex interpolation. Realizability of every relaxed vertex is not required.

## Complete actual source mass

For each nonunit old cofactor, bound its actual raw35 cylinder mass. Summing
the seven complete cofactor families gives

    Rraw=max_r sum_(R(l)=r)n_l +max_l n_l +max_l d_l/18
         +sum_l w_l/36 +max_r sum_(R(l)=r)w_l/36
         +max_l w_l/36 +1/72.

The terms correspond to3,9,3^a(a>=3),5^b,3*5^b,9*5^b, and3^a*5^b(a>=3,b>=1).
The denominators include their complete geometric exponent sums. An original
mixed7 label with exponent e removes ambient mass at most7^-e times its raw
old-cylinder cap. Its original residues remain independent of other labels.
The complete sum over positive e is1/6. The actual pure7 survivor mass is
at least5/6. Hence the complete actual357 mass is at least

    (5s-Rraw)/6.

Rraw is separately convex in the five parameter groups, as a positive sum
of maxima of separately affine expressions. The displayed lower bound is
separately concave. Its minimum at the2058 vertices is exactly19/108, with
54 equality vertices. At the first equality vertex554, s=1/3 and Rraw=11/18.
Successive vertex interpolation therefore proves the same mass lower bound
on the whole containing domain and on every actual source. Missing pure5 or7
only increases the relevant pure survivor lower bound, so this source
statement also includes those missing-class subcases.

## Same actual square and weighted deletion

An independent complete ternary test has a root r and cell j, giving

    b_l=1+1_(R(l)=r)+1_(l=j),
    r in{0,1}, j in{0,...,5}.

These are12 layouts. A test9 is retained even though the forbidden9 is
absent or ineffective. A missing test or one with empty restriction to the
survivors may be enlarged by an available root/cell test; this only raises
the complete nonnegative load. No identification of independent residues
is imposed. In particular j need not lie in root r.

Use source32's YC3 with the fixed Young weight t=1 for both roots. The
arbitrary-root geometric tail proof uses only the cell partition and
sum_(k>=0)3^(-k-3)[2(b+k)+1]=(b+1)/9, so it applies to these six cells. Put

    M=max_b[sum_l eta_l*b_l^2+max_l(b_l+1)/9],
    U_b=sum_l n_l*b_l^2+(1/4)sum_l eta_l*b_l^2
        +max_l[(d_l+1/4)*(b_l+1)/9]+(5/8)M,
    U=max_b U_b.

The selected zero7 old test has raw square at most U_b; each independent
positive7 old test has raw square at most U. The nested-interval comparison
used to derive YC3 bounds individual and pair indicator integrals; it does
not claim that actual five-coordinate residues are nested or equal.

Fix C=13591/468 and k_l=C-b_l^2>=0. The actual old test A0 has A0>=b_l,
so (C-A0^2)_+<=k_l. Retain SD3's seven weighted cofactor terms:

    W_b(C)=max_r sum_(R(l)=r)k_l*n_l +max_l k_l*n_l
           +max_l k_l*d_l/18 +sum_l k_l*w_l/36
           +max_r sum_(R(l)=r)k_l*w_l/36
           +max_l k_l*w_l/36 +(C-1)/72.

Every layout has cells with b_l=1, so max k_l=C-1. This is precisely the
weighted raw-cylinder cap used by SD3, now summed over six cells. Under the
product of the actual uniform35 law and actual pure7 law, the complete
positive7 cylinder caps sum to at most1/5, and their weighted square sum is
at most4/15. Source32's SD4/SD5 comparison therefore gives

    s E[(L^2-C)1_(actual mixed7 survivor)]
      <=(6/5)U_b+(7/15)U+W_b(C)/5-C*s.

Conditioning this exact product law on its actual mixed7 survivor gives
the complete actual uniform357 law. The mass result above supplies a
strictly positive denominator. No alternative normalized measure is used.

For this fixed C, all2058*12=24696 signed margins

    C*s-(6/5)U_b-(7/15)U-W_b(C)/5

are nonnegative. The minimum is zero, with108 equality pairs. The first is
vertex422/layout9, with s=25/72 and U_b=U=595/144. For every fixed layout,
U_b,U,W_b are separately convex: each is a positive sum or maximum of
separately affine terms. The signed margin is therefore separately concave.
Successive deterministic interpolation proves it throughout the continuous
domain. The exact vertex check supports this argument; it is not a substitute
for the actual-family extraction or for the interpolation proof. The
extremal relaxed tuples are not asserted to be actual families.

## Complete AP(4,4) consumer on this source

In the final fallback the first forbidden3,5,7 roots are all present, so the
actual source lies inside their product complement with pure masses
(2/3,4/5,6/7). Its normalized Haar density is at most108/19. The source35/236
increasing-convex comparison therefore gives

    H(t)=A E[(X3*X5*X7-t)_+],
    A=(108/19)*(2/3)*(4/5)*(6/7)=1728/665,

with auxiliary geometric-count caps(3/2,5/4,7/6). These auxiliary variables
are independent comparison variables; actual forbidden events are not
claimed independent. Quadratic hinges use the same prefactor and source,
and each individual hinge is also bounded by C-1. Taking the minimum of
these two bounds is legal on this one source.

Retain physical11/T4 and13/T4, with comparison caps5/3 and3/2, and condition
only once on the final common survivor. Source35's complete union estimate
recomputes the survival lower bound as

    rho=17435639/31281600=0.5573768285509693.

For each threshold16 and81, all low product probabilities are retained and
the full zeroth and second moments give the complementary infinite tails.
With the new source square and source hinges this yields

    Gamma13=153287599326830249/1376606275558371
           =111.35180919079758,
    T13(81)=117265021070648003186571145229272057
            /1852905919783748574479166178621875
           =63.28708857724084.

All complete supported hinges5,6,7,8 are recomputed with the same rho. The
unchanged17/19 row-potential constants then give the stated K. The19 input
is this new normalized13 law followed by the physical17 kernel; it is not
replaced by a killed17 subprobability. No old Gamma, survival denominator,
or tail is substituted into this changed source comparison.

The two complete core calculations directly reuse236's verified
core_errors routine. They retain its conservative global initial constants
D0=432/53 and G0=3849/106, and recompute every incoming,17/19 mask and full
ordered-pair test-tail contribution using the new Gamma13 and rho. Thus they
do not require a new claim about improved initial source-difference constants.
The boxes are[20,20,20,20,20,20,20]/current(8,8) and
[17,10,8,7,6,6,6]/current(6,6). Both preserve the first3,5,7 roots and pure9
status. Consequently the new complete comparison applies to both the full
and retained families, and both K+core-error values are below403.

## Exact certificate and boundary

The [helper](../../frontier/transport/missing9_six_cell_fallback.py) and
[certificate](../../certificates/source_norms/missing9_six_cell_fallback.json)
retain exact rational source margins, complete record digests, all equality
witnesses, complete AP probability tails, hinges and both core errors. The
helper reconstructs the2058 unweighted mass margins independently from
raw cylinder components and checks all24696 square margins at fixed C.
It does not repeat the earlier source-constant or threshold optimization.
The pinned236 probability, moment and core routines are reused directly;
its full dependency closure and first seven fallback records are preserved.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/missing9_six_cell_fallback.py --check
```

This is an ordinary continuous-domain proof with exact arithmetic evidence.
The conclusion closes these complete fallback comparisons and the last
branch's two finite-core criteria. It does not establish an effective9
comparison, a global continuation, a Lean theorem, or unrestricted Erdos7.
