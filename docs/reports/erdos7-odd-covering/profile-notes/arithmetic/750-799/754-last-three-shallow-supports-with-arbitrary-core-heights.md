# One actual source admits shallow multioutside originals on the last three axes

Let p1<...<p5 be five primes above7. Fix arbitrary finite core heights
E3,E5,E7 and the carrier

    Q=3^E3 5^E5 7^E7 product_(i=1,...,5) p_i.

Consider any finite family of pairwise DISTINCT odd numerical moduli
m>1 dividing Q, with globally fixed arbitrary residues. An original is
core-shallow when its3/5/7 exponents are at most(2,1,1). Assume every
core-shallow original has outside support either empty, a singleton, or
a subset of{p3,p4,p5}. Thus all three pairs and the triple among the last
three outside axes are allowed, for every old cofactor d|315, including1.
Every original which is not core-shallow may use ANY outside subset.
All eleven nonunit old-cofactor slots at each singleton outside axis are
allowed; there is no per-fibre bound on deleted roots.

Then the actual Haar survivor density is at least

    560/9561123 > 1/18000.                             (T)

The same bound holds when some coordinates or originals are absent, by
free-coordinate padding and supported auxiliary source pruning. This is
ONE scope: outside exponents are at most1 throughout. It does not assert
the corresponding arbitrary-height outside result, nor admit shallow
pairs involving p1 or p2. The argument is ordinary mathematics plus exact
finite certification, not Lean or unrestricted Erdős #7.

## Fix the actual core law before every query

For every actual family, choose ONE supported effective-padded source
by the six-shape construction in the [complete actual catalogue](753-six-shape-actual-source-joint-query-catalogue.md).
Missing or inactive7 slots receive auxiliary source restrictions; active
original phases stay fixed, including labels whose deletions overlap.
The catalogue enumerates these selected sources, not every raw unpadded
source vector. For each actual b, choose a uniform surviving-cell law except
for the116 listed exceptional b vectors, where use the assigned integer
weights. The source choice depends only on the actual pruned old315
configuration, not on subsequent free query phases or separate deletion
terms. Put

    w_x=v_x/D, D=sum_x r(x)v_x, t=max_x v_x.

For its eleven nonunit divisor slots define the exact cylinder cap
numerators C_d. In the fixed numerical order

    (3,5,9,15,45,7,21,35,63,105,315),

put

    M=sum_d C_d,
    K=sum_d k_d C_d,
    k=(0,12,24,12,42,8,8,22,36,22,57).

This one law has c=M/D, lambda_kappa=K/(48D), and raw core Haar
cap315t/D. Write J4,J6 for certified hinge numerator UPPER bounds, so
H4<=J4/D and H6<=J6/D. For uniform sources these are the actual sharp
numerators from the catalogue. For the116 exceptional sources set
J4=29t and J6=10t: each nonnegative query summand is multiplied by
v_x<=t, and the uniform sharp numerators of this SAME b are29 and10.
All cylinder caps are recomputed with the fixed weights0<=v_x<=120.
This is a pointwise comparison on one supported source; it does not reuse
an unchanged uniform normalized hinge after reweighting or claim the
weighted hinge upper bounds are sharp.

## Actual singleton fibres and clipping

It suffices first to use the reference outside primes11,13,17,19,23.
At each p exclude its actual pure root, or one auxiliary root if the
pure original is absent. Let nu_p be the uniform law on the p-1 live
roots. Write xi=(x,y7) for a full old315 cell; x is still the old45
coordinate indexing the weights. Let A_p(xi) avoid all actual core-shallow
singleton originals p*d, d|315, d>1, whose old condition contains xi. Write

    t_p(xi)=nu_p(A_p(xi)).

Use clipping thresholds a=(4,6,6,6,6),

    s_p=(p-a_p)/(p-1),
    f_p(xi)=min(1,t_p(xi)/s_p).

The singleton loss count q_p(xi) is bounded by a complete nonunit old315
query; its corresponding complete query is1+q_p. The same-source hinge
bound gives

    E_mu(1-f_p)<=H_(a_p)/(p-a_p).

Define ONE finite, unnormalized measure

    nu(dxi,dy)=mu(dxi) product_p
       [1_(y_p in A_p(xi)) f_p(xi)/t_p(xi) nu_p(dy_p)],    (U1)

with the p-factor zero when t_p(xi)=0. It is supported on the actual
old315 and singleton survivors. The last-three multioutside originals
have NOT yet been conditioned on; they will be deleted under this same
measure. Conditional factorization in(U1) is valid precisely for the
singleton constraints already imposed, not for those later deletions.

Put

    rho=(1/7,1/7,1/11,1/13,1/17).

Since0<=f_p<=1, the raw mass is at least

    1-rho1 H4-(rho2+rho3+rho4+rho5) H6.               (U2)

For every old cylinder C and outside support J,

    nu(C times one outside query cylinder on J)
       <=mu(C) product_(i in J)rho_i.                (U3)

This follows directly from f_p/t_p<=1/s_p; unqueried factors integrate
to f_p<=1. The raw Haar cap is

    D0=(315t/D) product_i p_i/(p_i-a_i)
      =(315t/D)(437/49).                            (U4)

The source is never normalized in the budget below.

## Joint payment for higher-core and shallow multioutside originals

Uniformly extend nu in all extra core digits. For a shallow core divisor
d, a positive extra exponent is possible only on its saturated primes.
The geometric sum over nonempty extra supports/depths is exactly

    kappa(d)=product_(p saturated in d)(1+1/(p-1))-1.

Different numerical original labels at fixed excess vector remain
distinct saturated slots. Equation(U3), the same old cylinder caps, and
the complete geometric sums therefore give total higher-core deletion
mass at most

    F lambda_kappa,  F=product_i(1+rho_i)=27648/17017. (U5)

This includes every outside support for those higher-core originals.
It sums uniform upper bounds for the actual fixed residues; it does not
replace the actual family by independently attained source optima.

For each allowed shallow multioutside support J subset{3,4,5}, |J|>=2,
there is at most one numerical original d product_(i in J)p_i for each
d|315. Their total actual mass is bounded by the complete old query,
including its unit slot. Thus(U3) bounds all these deletions by

    B(1+c),
    B=product_(i=3,4,5)(1+rho_i)-1-sum_(i=3,4,5)rho_i
     =42/2431.                                     (U6)

These are separate numerical originals from the singleton and
higher-core classes. Their overlaps can only improve the union bound.
Every cost is charged to the SAME measure(U1).

Consequently the actual raw survivor mass is at least1-L, where

    L=F lambda_kappa+B(1+c)+rho1 H4+sum_(i=2,...,5)rho_i H6.

The certified hinge numerator bounds of the chosen source give L<=cost,
where

    cost=(294D+576K+294M+2431J4+6288J6)/(17017D).

Define the exact integer reserve

    G=16723D-576K-294M-2431J4-6288J6.                 (U7)

It is enough that G>0. Dividing the raw reserve by(U4), the corresponding
actual Haar bound is EXACTLY

    (1-cost)/D0=G/(47805615t).                       (U8)

The integer objective includes a valid bound for the same weighted H6.
No independence of the deletion events or equality of unrelated extrema
is assumed.

## Exact certification of every actual source

The3193 catalogue groups record the exact uniform(N,M,K,J4), each with
its own actual b realizations and H6 numerator10. All112,777 sources
outside the explicitly listed116 exceptions already have G>0 under
their uniform law. The exceptions are exactly:

- shape4:63 sources with(N,M,K)=(75,146,1873),21 with(75,147,1873);
- shape5:24 sources with(75,146,1873),8 with(75,147,1873).

All116 have exact uniform J4=29; replacing29 by28 would be invalid.
The fixed weighted dictionary covers every one of them exactly once.
Its literal b vectors are matched against the complete native catalogue,
which establishes actual source membership. The consumer recomputes
all eleven caps for each fixed weighted law and uses the pointwise
bounds J4=29t,J6=10t. Their worst certified cost upper bound is
532900/561561<1; their minimum paired Haar lower bound is57322/47805615.

The uniform nonexception minima, paired with each source's own Haar cap,
are:

|shape|uniform sources|minimum paired Haar bound|
|---|---:|---:|
|0|19324|84749/47805615|
|1|20279|32689/15935205|
|2|20080|32689/15935205|
|3|18025|560/9561123|
|4|17685|5692/47805615|
|5|17384|5692/47805615|

The least value across all assigned sources is560/9561123, giving(T).
Equivalently every source has G>=2800t. Reweighted sources have the
stronger G/t>=57322. These are feasibility certificates, not optimality
assertions. Numerical weight search is not an input to the checker.

## Larger ordered primes and finite-height scope

For any five ordered outside primes above7, their ordered values are at
least11,13,17,19,23. Keeping the same thresholds by position,

    rho_i=1/(p_i-a_i),
    p_i/(p_i-a_i)=1+a_i/(p_i-a_i)

both decrease as p_i increases. Every coefficient in(U2),(U5),(U6) is
nonnegative, so the total cost and the Haar cap cannot increase. The
same assigned core laws prove the same lower bound for every such
ordered prime set. This transports the whole joint cost, not only one
marginal parameter.

The extra3/5/7 tails were summed to infinite geometric majorants, so every
finite core height is covered uniformly. If the actual carrier has smaller
core exponents or missing outside coordinates, lift to the padded carrier;
actual Haar survivor density is unchanged by such free-coordinate lifting.
Supported auxiliary source restrictions can reduce the chosen source but
cannot create survivors outside the actual original family.

The [continuation consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_last_three_bridge.py)
uses the [116 fixed source laws](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_last_three_weights.json)
and emits the [exact continuation result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_last_three_bridge.json).
Run from the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_last_three_bridge.py
```

This consumer pins the complete Report753 catalogue and its producer,
checks every uniform group and literal weighted source, recomputes all
weighted caps and(U2)--(U8) in exact rational arithmetic, and rejects
stale inputs or results. It does not rerun Report753's native enumeration;
that report's separate consumer reconstructs the complete catalogue.
Weighted hinges are proved by pointwise domination, so weighted query
pair enumeration is unnecessary. Independent native catalogue reconstruction
and independent rational checks reproduce the uniform theorem constant.
This is ordinary proof and exact finite certification, not Lean verification.

Compared with [Report751](751-clipped-common-sources-release-core-and-outside-heights.md),
this theorem admits every shallow pair and triple among the last three
outside axes, while keeping those outside exponents at most1. It does
not combine that enlargement with Report751's full-height outside cases.
[Report752](752-joint-deletion-credit-distinguishes-equal-marginal-sources.md)
shows why unrestricted joint shallow constraints need information beyond
conditional singleton marginals. The unrestricted Erdős problem remains open.
