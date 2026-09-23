[Index](../../marked_head_profile.md) · [Fixed physical chain](333-variable-full-haar-thresholds-retain-more-survivor-mass.md) · [Original AP blocks](335-original-ap-blocks-sharpen-the-fixed-full-haar-account.md)

# Fixed original groups retain the complete count law

Keep333's same finite effective9 source guard

    qJ>=1-1/4000, rho>=1/10,

the supported AP11/T4--AP13/T5 law, and the full-Haar thresholds
(6,6,8,12,12,16,18,24,24) at(17,19,23,29,31,37,41,43,47).
We extend335's original-label account to any preselected finite group
of the prior comparison factors. The numerical instance below groups
ALL prior factors at each target and keeps every count and original
exponent tail. It changes no actual kernel or own-test residue.

Taking the smaller of this tested bound and the existing333/335 bound
at each step gives actual surviving mass through43 at least

    0.05848024855474408846518351080...,

with the exact fraction in the certificate governing the decimal.
At47 the all-prior bound alone is

    -0.01141641419377879947721177565...,

and the rowwise minimum gives

    -0.01141542774955686656823162586... .           (G1)

These improve335's same-chain account. The positive magnitude of the
last number remains the required strict budget for an additional
same-chain correction. The tested grouping and fixed threshold
sequence do not establish survival through47. No optimization over
all groups, partitions or thresholds has been performed, and no
claim that every count regrouping must fail is made.

## A complete operator for a preselected original group

Choose a finite group G of prior comparison factors(p,c_p), with
0<=c_p<=p. Each auxiliary count has

    Pr(N_p=1)=1-c_p/p,
    Pr(N_p=n)=c_p(p-1)/p^n, n>=2.

Let N_G=product_(p in G)N_p and m_G=E N_G. The auxiliary counts are
independent solely for the established conditional comparison. The
actual source, masks and physical kernels keep their original joint
law. A group and its original test labels are selected before the
auxiliary counts or source point are sampled.

An original exponent tuple a=(a_p) is active when a_p<N_p for every p.
For a threshold r>1 put

    p_a(n)=Pr(a active,N_G=n), w_a=Pr(a active),
    Q_a,r(v)=E[1_(a active)
                   ((N_G v-r)_+-(N_G-r)_+)/N_G].      (G2)

For each original tuple, its357 cofactor test is the same test across
every auxiliary outcome activating that tuple. It need not agree with
the test of another tuple. Reuse06(FL1)'s original-label Jensen step
in precisely this order, as in335(A1)--(A3).

Put k=ceil(r). On v>=1 the exact cost is

    Q_a,r(v)=sum_(n<k)p_a(n)(v-r/n)_+
                     +[w_a-sum_(n<k)p_a(n)](v-1).    (G3)

All coefficients are nonnegative. Thus Q is increasing, convex and
zero at one, as required by329's centered source transport. Only tuples
with product_p(a_p+1)<k can occur in a count outcome n<k. The remaining
tuples contribute exactly w_a(v-1). The identities

    sum_a w_a=m_G,
    sum_a p_a(n)=n Pr(N_G=n)                         (G4)

count the original active labels in each outcome. In particular, the
full omitted-tuple coefficient is

    R_G=m_G-sum_(product(a_p+1)<k)w_a>=0.             (G5)

These are complete sums, not a truncation of original moduli. Every
finite family is embedded by completing absent original labels in
advance; the added centered terms are nonnegative. On a fixed finite
physical source the loads are bounded and sum_a w_a is finite, which
justifies collecting the nonnegative terms and taking these limits.

Let B_theta be the established complete raw357 operator at a whole-J
source vertex. Define the finite, fully paid expression

    V_theta(G,r)=sum_(product(a_p+1)<k)B_theta(Q_a,r)
                         +R_G B_theta(v-1).          (G6)

Here B_theta(v-1)=13/20. The raw comparison including its constant is
(1/4)E(N_G-r)_++V_theta(G,r). For G={11,13}, this is exactly335's
existing original AP block operator. Empty or zero-active groups use
the same formulas; zero-active tuples have zero cost.

## Exact recursive enumeration and complete tails

The tuple enumerator keeps a remaining product budget k-1. Choosing
a_p+1=n replaces that budget by floor(budget/n). It therefore lists
exactly product(a_p+1)<=k-1 without a k^|G| Cartesian scan.
The finite count probabilities use the same remaining-product rule,
also respecting N_p>=a_p+1. Their complement within w_a is the exact
active tail in(G3); the remaining original tuples are paid by(G5).

For the tested all-prior groups the inventories are:

| Target prime | Group size | Threshold | Original tuples in(G6) |
|---|---:|---:|---:|
|17|2|6|10|
|19|3|6|16|
|23|4|8|43|
|29|5|12|141|
|31|6|12|201|
|37|7|16|575|
|41|8|18|1123|
|43|9|24|2533|
|47|10|24|3386|

The helper independently reconstructs the complete group count law,
checks both identities in(G4) at every finite count, evaluates the
nonnegative weighted hinges using the existing w357 operator, and
pays the entire(G5) term. Its certificate records exact totals and a
deterministic digest of the original-tuple coefficient inventory.
This calculation is an operator bound, not an enumeration or
realizability certificate for actual congruence families.

## A fixed group inside the same sole13 conditioning argument

More generally, partition the prior comparison factors into a fixed
group G and remaining factors with product Z. For a target threshold t,
write q_z=Pr(Z=z), U1=E[Z;Z>=t]. Keep333's actual source mass S,
lambda=1+7/4000, mean excess M, and denominator E(S)=eS-Ddelta.
The complete raw centered constant is bounded by

    C_theta=lambda*sum_(z<t)q_z*z*V_theta(G,t/z)
                            +U1*m_G*M,
    C=max_theta C_theta.                            (G7)

For z<t, the centered costs in(G3) are transported with lambda.
For z>=t the compared hinge is affine because every original source
load includes its unit; U1*m_G*M pays that entire outer tail. Constants
are transported with actual mass S. The nine whole-J vertex bounds
cover the same containing source face because the centered costs are
nonnegative convex inputs to the established separately convex source
operators. Selecting different maximizing own tests at different outer
z is permitted as an upper relaxation; no actual labels are identified.

Let W=N_G Z be the product of ALL prior comparison factors. Set

    c=E(W-t)_+,
    f=E(Z_post13-t)_+,

where Z_post13 includes exactly the preceding post13 factors, regardless
of the chosen group G. Only f is a pointwise floor at a through13
input. Grouping factors differently does not permit replacing it by
E(W-t)_+ or by an unrelated outer product.

The same nonnegative centering before the sole13 normalization used
in335 gives

    H_<p,t<=f+[C+(c-f)S]/E(S).                      (G8)

All physical kernels extend by their same normalized rule to inputs
removed at11/13, so the raw comparison and the subtraction of the
post-only floor apply on the same space. No later killed mass enters
the denominator. The helper checks c>=f>=0, a nonnegative shifted
numerator and e*C+(c-f)Ddelta>0. Thus(G8) decreases with actual S and
can be evaluated at333's same Smin.

In the tested all-prior instance, G contains every prior factor and
Z=1, so(G7) reduces to C=lambda max_theta V_theta(G,t). The
post13 floor in(G8) is still generally nonzero and remains unchanged.

## The computed same-chain improvement and its boundary

Use the unchanged charge factor1/(p-1-t_p) from333. All bounds refer
to the same incoming FULL physical law and every original own test.
It is therefore valid to take their minimum separately at each step
and then use the same cumulative union bound. The selected sources are

| Target prime | Selected bound |
|---|---|
|17|335 and all-prior agree|
|19,23,37|335|
|29,31,41,43,47|all-prior|

The uniform through43 lower and the remaining47 deficit are(G1).
No scratch three-factor estimate is needed for these minima. The
all-prior choice is not uniformly better in every row: moving a tail
inside a grouped source cost can replace the sharper finite-source
mean M by a lambda-scaled vertex mean. Retaining the minimum preserves
the proven stronger estimate for those rows without changing kernels.

The negative47 value settles only these computed bounds for this fixed
schedule and tested grouping. Other group choices, sharper source
operators or relations involving actual future tests remain outside
this calculation. In particular it does not construct a covering
family or establish that the sufficient bounds are jointly attainable.

The [portable exact helper](../../frontier/cover-geometry/high_rho_fixed_original_groups.py)
provides the reusable fixed_group_centered operator and the fixed
all-prior instance. The [canonical certificate](../../certificates/source_norms/cover-geometry/high_rho_fixed_original_groups.json)
binds the current333/335 sources, ordinary proof and producer. There is
no new Lean declaration or floating-point threshold search.

```sh
python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/high_rho_fixed_original_groups.py --check
```
