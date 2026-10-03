# Repeated upper-mass comparison lowers the fourteen-prime tail cutoff

Let C be a finite family of pairwise-distinct odd numerical moduli greater
than one, with one fixed residue per modulus. Assume at least one of
3,5,7,11 is absent from the ENTIRE original LCM, and at most fourteen
support primes are at most20000. Then C is noncovering. All original
finite prime-power heights, mixed supports and finite numbers of larger
primes are unrestricted. A constructed distorted survivor submeasure
has mass greater than1/7000; this is not a Haar-density assertion.

This improves the cutoff50000 in
[772](772-eleven-through-fourteen-prime-heads-admit-an-unrestricted-larger-tail.md)
to20000, with the same missing-small-prime restriction. The improvement
reuses the [weighted upper-quantile principle](../../001-064/04-the-weighted-upper-quantile-lemma.md)
(VH3,VH13) and the full query interface of
[771](771-stop-loss-profiles-preserve-the-ordinary-source-through-thirteen-primes.md).
The new content is their repeated application to that physical source,
with exact common-mass selection after every deletion. It is ordinary
mathematics and rational arithmetic, not a new abstract quantile theorem,
Lean verification or a resolution of unrestricted Erdős#7.

## Keep the comparator at the actual certified source mass

Let Pi be a positive finite measure on[1,infinity), of total mass A and
finite first moment. Suppose ONE physical source mu has exact mass m,
0<m<=A, and for EVERY complete numerical query Phi and nonnegative
increasing convex f,

    integral f(L_Phi) dmu <= integral f(z) dPi(z).       (1)

Write Top_m(Pi) for the largest m units of Pi's mass, splitting a cutoff
atom when necessary. For every t>=0 and s>=t,

    integral(L_Phi-t)_+ dmu
       <= integral(L_Phi-s)_+ dmu+m(s-t)
       <= H_Pi(s)+m(s-t),                              (2)

where H_Pi(t)=integral(z-t)_+dPi. If c is an upper-m cutoff, minimizing
the right side gives

    H_Top_m(Pi)(t)=inf_(s>=t)[H_Pi(s)+m(s-t)].           (3)

For t>=c this is H_Pi(t); for t<c it is H_Pi(c)+m(c-t).
Equal mass and the stop-loss representation of an increasing convex
function on[1,infinity) therefore give full comparison by Top_m(Pi).
This also follows from the existing upper-quantile principle. The
comparison is uniform over queries: neither mu nor the cutoff depends
on Phi or f. The upper submeasure itself attains this bound within the
abstract scalar comparison class; actual CRT sharpness is not asserted.

Removing LOW comparison atoms does not say that the actual deletion
removed low-load physical points. It assigns the certified retained mass
to the most expensive comparison locations. No matching between actual
points and comparison atoms is assumed.

If a source theorem only supplies nu of mass v>=m0, choose the single
scalar multiple mu=(m0/v)nu. This preserves avoidance and every
nonnegative comparison inequality. It is an existence construction for
each fixed original family, not an executable claim that an internal
observer has a free exact mass measurement.

## Update one physical law and then trim one outer comparison

At stage i suppose mu_i and Pi_i both have mass m_i, with(1) for every
query. Choose0<delta_i<1 and C_i=1/(1-delta_i)<=q_i. Put

    T_i=delta_i(q_i-1),
    D_i=H_Pi_i(T_i)/[(1-delta_i)(q_i-1)],
    m_(i+1)=m_i-D_i>0.                                (4)

The actual normalized clipping kernel of771, followed by actual
restriction, loses at most D_i. Its full-query comparison before the
restriction is the product of Pi_i and pi_cap(q_i,C_i), carrying the
scalar product z(1+J). The two Jensen steps from771 still apply: different
current-exponent old layouts are not identified with one layout, and
their sum at a fixed auxiliary run is bounded before applying(1).

Restriction preserves every nonnegative comparison. If its actual mass
is v_(i+1)>=m_(i+1), scale the restricted source by the ONE scalar
m_(i+1)/v_(i+1). Apply(3) to obtain

    Pi_(i+1)=Top_m_(i+1)(Pi_i times pi_cap(q_i,C_i)).    (5)

Thus ONE supported source serves every cost, query and later operation.
The old marginal is allowed to change under restriction and scaling;
no theorem requiring its preservation is being invoked here. Trimming
acts on the auxiliary comparison only. The original numerical labels,
fixed phases and all finite heights are unchanged.

For an actual added prime r>=q_i, use the same reference Pi_i and delta_i.
Its capped auxiliary tails C_i/r^e decrease; its threshold and loss
denominator increase. Therefore the actual loss is no greater than D_i,
and the actual full-query comparison is still bounded by the reference
product in(5). The same target m_(i+1) can be used for scaling. This
argument does not require a separate monotonicity theorem for Top.
Prefix-injection averaging also preserves the universal comparison and
prescribed mass, since every selected source works for every pulled-back
query and has the same exact mass before averaging.

## A finite state with complete infinite moments

For these integer-valued comparison loads, retain total mass m, complete
first moment W, complete second moment G and exact atoms pi_n for
1<=n<=N. The moments include the ENTIRE infinite auxiliary tail.
Appending pi_cap(q,C) multiplies these three quantities by

    1, 1+C/(q-1), 1+C(3q-1)/(q-1)^2,

and gives each new low atom by multiplicative convolution. For T<=N,

    H(T)=W-Tm+sum_(n<T)(T-n)pi_n.                      (6)

To trim to m', remove the low atoms in increasing order until exactly
m-m' mass is removed, splitting the last atom. Subtract the corresponding
exact first and second moments from W,G. The checker must establish that
this removal finished within its atom inventory. A missing cutoff is a
failed computation, not permission to discard the remaining tail.

Here N=100 resolves every cutoff and query. It is a bound on the stored
low comparison values, NOT on original prime-power exponents. Product
moments and the retained high comparison tail remain exact at every step.

## Two exact fourteen-prime continuations

First use the original763/771 source and its C17=4/3 cap. Its initial
certified mass is10237584019/168750000000. Initial upper-m selection cuts
at8. Fixed half clipping at31,37,41,43,47,53 gives successive trim cutoffs

    8,12,12,16,30,96,

and final mass0.0005647768194616365...>1/1800. This extends the fixed-half
old-source calculation itself through53; without repeated trimming,
771's corresponding sufficient ledger is negative.

For the sharper tail result, use
[770](770-an-eight-prime-source-with-threshold-six-at-seventeen.md)'s
source, with C17=8/5 and initial mass89120862071/1350000000000. Keep its
matching caps and complete comparator. At31,37,41,43,47,53 choose

    delta=(2/5,4/9,9/20,4/7,12/23,8/13).               (7)

The thresholds are12,16,18,24,24,32. The initial cutoff is8, and the six
post-operation cutoffs are8,12,12,16,24,48. Exact rational evaluation gives

    m14=0.0036313531285237293... >363/100000,
    G14=30.54613059504562... <611/20.                   (8)

These are the mass and square-query bound of the SAME constructed law.
The decimal displays are not used for the final inequality: all stage
fractions, moments and comparison atoms are retained in the exact result.
No optimality of this source or clipping schedule is claimed.

## The complete larger-prime tail

Collect every actual support prime at most20000 and pad to fourteen with
unused odd primes at most20000, excluding a chosen missing prime from
{3,5,7,11}. The sorted tuple dominates

    (3,5,7,13,17,19,23,29,31,37,41,43,47,53).

All other actual primes exceed20000. Artificial coordinates introduce
no new original classes; each original keeps its full finite exponent
vector and is processed at its largest exposed coordinate. An avoiding
point projects back to the original finite CRT carrier.

Apply the quarter-clipped larger-prime tail of772 to the same final
mass and G in(8). Its inherited complete analytic allowance is

    tau4(B,ell)=1/B * [(2ell^2+1)/(2ell^2-1)]^4
                     * [B/(B-1)]^2
                     * sum_(h=0..4) 4!/[(4-h)!ell^h].

For B=20000,ell=9 the domain conditions B>=286 and3^ell<=B hold. The
exact final reserve is

    m14-(4/3)G14*tau4(20000,9)
       =0.00014539369830643227... >1/7000.             (9)

The majorant pays every possible larger prime, hence every finite
actual tail, with all old cofactors and full finite heights. The source
geometry and analytic prime-product estimate are inherited proof
premises. The arithmetic consumer does not claim to regenerate them.

## A precise remaining obstruction of this comparison interface

For an equal-mass comparison Pi on[1,infinity), let W be its first
moment. There exists SOME legal constant clipping parameter giving a
positive one-step sufficient ledger at a prime q exactly when

    W<(q-1)m.                                         (10)

Indeed H_Pi(T)>=W-Tm, whereas positivity requires
H_Pi(T)<m(q-1-T). Conversely, when(10) holds choose
0<T<min(1,(q-1)^2/q). Then H_Pi(T)=W-Tm, and delta=T/(q-1)
satisfies the cap domain and gives a positive remaining ledger.
This is a criterion for the declared bound, not for actual noncoverage.

The original source's initial mass-conditioned comparison has
W/m=14.772109001867241...>10. Therefore inserting a fresh11 coordinate
from THIS interface fails for every constant delta. Exposing11 last is
algebraically legal if all its originals retain their complete earlier
cofactors; its failure here is quantitative. A better same-law source
comparison or further original-query relations are needed.

After the old fixed-half fourteen-head schedule the comparator has
loads at least96, so(10) excludes any next59 clipping parameter.
After(7), its mean is77.40254459037625...>58, again excluding every
next59 parameter for that fixed predecessor. Earlier schedule changes,
different sources and sharper phase-dependent loss estimates remain
outside these obstructions.

## Verification and scope

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_mass_trim.py)
pins and freshly invokes772 and its complete supplier chain, then
reconstructs both repeated mass-trim schedules and the complete tail
inequality. The [retained exact result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_mass_trim.json)
contains the low atoms, complete moments, split cutoffs, stage charges,
final reserve and first-moment gate differences. The inherited source
route rejects Python-O; new checks are explicit exceptions.

An independent divisor-sum convolution and cumulative-cutoff calculation
matched every stage charge, cutoff, removed first/second moment and
retained moment for(7), and the tail value(9). Another implementation
matched the old fixed-half masses and cutoffs. These are exact arithmetic
checks of the retained construction, not finite-family tests standing in
for its quantified ordinary proof.

Repeated upper-mass comparison improves an outer bound. It does not
restore the phase-indexed intersections needed for exact deletion-credit
updates; the actual-pair obstruction in
[755](755-current-query-maxima-are-not-a-closed-continuation-boundary.md)
still applies to its stated summaries. The all-four-small-primes source,
universal actual-dictionary feasibility and unrestricted Erdős#7 remain
unresolved.
