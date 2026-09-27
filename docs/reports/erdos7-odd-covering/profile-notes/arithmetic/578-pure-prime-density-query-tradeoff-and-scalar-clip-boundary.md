# Exact pure-prime density/query tradeoff and a scalar-clip boundary

These are ordinary mathematical proofs with exact finite diagnostics, not
new Lean verification. Original phases are fixed once. Every constructed
source is one probability law used unchanged in later queries.

[Chapter03, sections HC1--HC7](../../problem-details/03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md#sharp-tail-profiles-of-maximal-cylinder-caps), already supplies the homogeneous comb capacity
comparison, a constructive capped source, the pure residual Haar source,
the sharp finite-head comb query minimum, and the unbounded-height
obstruction to improving its marginal-cap envelope. In particular HC4--HC5
already uses the equally split spine source, and HC7 gives the stronger
fixed convex-cost asymptotic boundary. Those results are reused here;
neither the comb nor the lack of a uniform scalar saving is claimed as
new. Their named existing Lean declarations are
`HomogeneousCombCapacity.comb_le_actual_prefix_flow`,
`PrefixCapacityRealization.exists_comb_capped_probability`, and
`PurePrefixResidualLaw.exists_exact_residual_law`. No new Lean closure for
this report is claimed.

The additional quantitative result is an exact finite-height joint
tradeoff between the complete query sum and a density cap, for arbitrary
prime p>=3, together with a consumer that excludes all pure-source and
height-cap repairs of the current height-three single-clip envelope.

## 1. The source problem and exact tradeoff

Fix a prime p>=3 and Haar probability h_p on the p-adic integers. A finite
pure family F has at most one forbidden class modulo p^e at each depth
1<=e<=H. Nested and redundant classes are allowed. Let S_F be its actual
complement. For a probability u supported on S_F define

    M_e(u)=max_(r mod p^e)u([r]_(p^e)),
    R_p(u)=sum_(e>=1)M_e(u).

The density restriction u<=D h_p is a measure inequality, not a condition
on root masses alone. Set

    D_min(p,H)=(p-1)/(p-2+p^(-H)),
    D_star(p,H)=(p/(p-1))^H,
    A_star(p,H)=[1-(p-1)^(-H-1)]/(p-2).

For H>=1 and D>=D_min, the exact worst-case optimum is

    sup_F inf_(u supported on S_F, u<=D h_p) R_p(u)
      = max{1/(p-2)-D/[(p-2)(p-1)p^H], A_star(p,H)}.        (PT1)

The infimum of an empty feasible set is infinity. For D<D_min the
supremum in PT1 is infinity. Without any density restriction its value is
A_star(p,H), even if singular probability laws are allowed. These are
worst-case statements over actual families; different families need not
have equal optima. One fixed comb attains the worst case.

## 2. Constructing one source for every finite-height family

The complete pure deletion has Haar mass at most sum_(e=1)^H p^(-e).
The existing normalized pure residual Haar law u_0 therefore satisfies

    u_0<=D_min h_p,
    R_p(u_0)<=D_min/(p-1)=1/(p-2+p^(-H)).                  (PT2)

There is also an explicit (p-1)-ary allowed subtree. At each retained
prefix of depth e-1 there are at least p-1 legal children: ancestors are
already legal, and the whole tree has at most one new forbidden child at
depth e. Choose p-1 legal children and split the parent mass equally.
Continue to depth H, then use Haar inside each retained leaf. The choices
are made once, before any query. Call this law u_*.

Every retained depth-e prefix, e<=H, has mass (p-1)^(-e). For e>H its
maximum cylinder mass is (p-1)^(-H)p^(H-e). Hence

    u_*<=D_star h_p,
    R_p(u_*)=sum_(e=1)^H(p-1)^(-e)+(p-1)^(-H-1)
            =A_star(p,H).                                (PT3)

This elementary construction is the allowed-tree version of the existing
split-spine source. For H>=2 and D between D_min and D_star, set

    lambda=(D-D_min)/(D_star-D_min),
    u_D=(1-lambda)u_0+lambda u_*.

Cylinder maxima, and thus their nonnegative sum, are convex in u. Both
endpoint bounds lie on the line
A=1/(p-2)-D/[(p-2)(p-1)p^H]. Consequently

    u_D<=D h_p,
    R_p(u_D)<=1/(p-2)-D/[(p-2)(p-1)p^H].                  (PT4)

For D>=D_star use u_*. When H=1 the endpoints coincide; use u_* directly
and do not divide by D_star-D_min. This proves the upper half of PT1.

## 3. The existing comb gives exact lower bounds including the Haar tail

Use the distinct pure originals

    C_e=[p^(e-1)]_(p^e), e=1,...,H.

This is the existing homogeneous comb after a prefix-tree relabelling.
The C_e are disjoint because their first nonzero base-p digit is 1 at
different depths. Define

    Z_H=[0]_(p^H),
    E_(e,d)=[d*p^(e-1)]_(p^e), 1<=e<=H, 2<=d<=p-1.

Its actual survivor is the disjoint union

    S_H=Z_H disjoint-union union_(e,d)E_(e,d).              (PT5)

It has Haar mass (p-2+p^(-H))/(p-1), forcing D>=D_min for any supported
density-D probability.

For an arbitrary supported probability u, write Z_e=u([0]_(p^e)),
Z_0=1. At depth e the spine has a zero-mass forbidden child, its
continuation of mass Z_e, and p-2 exits of total mass Z_(e-1)-Z_e.
Therefore

    M_e>=max{[Z_(e-1)-Z_e]/(p-2), Z_e}.                   (PT6)

Partitioning a depth-H cylinder of maximum mass into p^n descendants
shows M_(H+n)>=M_H/p^n. Thus the complete tail, not just the finite
head treated in HC4--HC5, contributes

    sum_(j>H)M_j>=M_H/(p-1)>=Z_H/(p-1).                  (PT7)

Let c_e=[1-(p-1)^(-(H-e+2))]/(p-2), e=1,...,H+1. Then
c_(H+1)=1/(p-1), (p-1)c_e-1=c_(e+1), and 0<=(p-2)c_e<=1.
Combine the two inequalities in PT6 with weights (p-2)c_e and
1-(p-2)c_e to obtain

    M_e>=c_e Z_(e-1)-c_(e+1)Z_e.

Summation and PT7 telescope to

    R_p(u)>=c_1 Z_0=A_star(p,H).                          (PT8)

This applies to every probability, including singular ones; infinite
R_p automatically satisfies it.

For a density-D probability, PT5 also gives
sum_(e=1)^H M_e >= (1-Z_H)/(p-2). Add PT7 and use Z_H<=D p^(-H):

    R_p(u)>=1/(p-2)-Z_H/[(p-2)(p-1)]
            >=1/(p-2)-D/[(p-2)(p-1)p^H].                 (PT9)

Both lower bounds are attained. On the comb, the split-spine law puts
mass (p-1)^(-e) on each exit E_(e,d) and mass (p-1)^(-H) on Z_H,
using Haar inside each member. An earlier exit at depth j contributes
(p-1)^(-j)p^(j-e)<=(p-1)^(-e) to a depth-e cylinder. Its density maximum
is D_star. Normalized Haar has maxima D_min p^(-e), attained at the
SAME exit E_(e,2) for e<=H. Above H both laws attain their maxima on a
common descendant of E_(H,2). Their mixture therefore has exactly

    density max=(1-lambda)D_min+lambda D_star,
    R_p=(1-lambda)D_min/(p-1)+lambda A_star.

This attains PT9 up to D_star and PT8 thereafter, proving PT1.

## 4. Relation to the existing all-height obstruction

The limit A_star(p,H)->1/(p-2) recovers the existing scalar obstruction.
In particular, no source chosen on every finite pure ternary survivor
can have a uniform R_3<=A<1, even with no density restriction. This is
already implied by Chapter03 HC4 and HC7, and is not a new conclusion.

The finite-density formula additionally quantifies the tradeoff. A fixed
D<(p-1)/(p-2) fails feasibility for sufficiently long combs. For any
fixed D>=(p-1)/(p-2), PT1 tends to 1/(p-2) with its exact density term.
At an individual finite height, however, source reweighting does improve
the query sum. PT1 states exactly how much can be guaranteed uniformly
at that height and density.

## 5. An exact height-cap tradeoff already at H=2

Now fix just the two pure originals 1 mod3 and 3 mod9. The allowed
modulo-nine residues are {0,2,5,6,8}. Let

    A=R_3(u), theta=sum_(e>=4)M_e(u), m=M_2(u).

For every supported probability m>=1/5. Its ternary root0 has at most
two allowed depth-two cells, while root2 has three. Thus

    M_1 >= max{1/2,1-2m},
    A >= max{1/2,1-2m}+(3/2)m,
    theta >= m/6.                                        (PT10)

The last two statements include the complete infinite query tails,
using descendants of a depth-two maximum cylinder. They need no
density bound.

For 1/5<=m<=1/4 assign mass m to each of cells0,6 and mass
(1-2m)/3 to each of cells2,5,8; use Haar inside every cell. Then

    M_1=1-2m, M_e=m*3^(2-e) for e>=2,
    A=1-m/2, theta=m/6.                                  (PT11)

For m>=1/4, the source at m=1/4 simultaneously has no larger A and
theta. Therefore PT11, m in[1/5,1/4], is the exact set of undominated
(A,theta) pairs. This handles arbitrary height-dependent caps: any
valid such caps dominate the actual M_e, so they cannot improve this
frontier after their complete high tail is summed into theta.

## 6. Consequence for the existing height-three scalar clip

Keep the SAME Q-source used by Report574 and its current uniform bounds

    R_Q(nu)<=B,
    B=432040125182653876501/86355045355449035400,
    E_nu(L-t)_+<=K_t.

Each one-phase Q query load has this bound. Convex mixtures of such
loads have it as well. If the through-exponent-three projected phases
are removed by the existing PA source, the source-only complete-tail
cap bound is

    1-c(x) <= sum_(e>=4)M_e(u)L_e(x) = theta Y(x),

where Y is one convex mixture fixed by the chosen u and original
phases. This changes neither u nor nu. For real t>=0 with kappa=1-theta*t>0, the
same actual clipped submeasure

    eta=u nu chi / max(c,kappa)

has the certificate

    R_P(eta/eta(1))
      <= C(A,theta,t)
       = [kappa B+A(1+B)]/[kappa-theta K_t],              (PT12)

when its denominator is positive. This is the existing proof template,
with its constants exposed. C is increasing in A and theta, since

    partial_theta C
      = [B K_t+A(1+B)(t+K_t)]/[1-theta(t+K_t)]^2 >=0.

PT10--11 therefore reduce the BEST certificate obtainable by changing
only the pure source or its height caps to m in[1/5,1/4], with
A=1-m/2 and theta=m/6. On this curve the sign of partial_m C is
the sign of

    (1+B)(t-3)+(1+2B)K_t.                                (PT13)

For t>=3 it is nonnegative. On 0<=t<=3, the existing exact K envelope
has K_t>=K_3, and

    (1+2B)K_3-3(1+B)
      =52828828309709262307189429011668301174407
        /10282123892873170813251654926015586631375 >0.

Thus m=1/5, the normalized Haar source for this two-class pure comb,
minimizes the current certificate for each admissible t. In particular,
optimizing the pure source alone cannot improve it. At m=1/5,
A=9/10, theta=1/30, and its exact global minimum over admissible real t>=0 is

    t=3,
    min C=5661267838960687810116513
           /474307692534412983430090
         =11.935854990481605...,
    min C-566/49
      =8943970134595954074278197
        /23241076934186236188074410 >0.                   (PT14)

Here the existing K_t is affine between consecutive integers. Corner
(x,y)=(1/2,2/3) dominates at all endpoints0,...,7, hence throughout.
On every unit interval C is a ratio of affine functions with positive
denominator, so its derivative has constant sign. Checking these
endpoints gives the minimum on[0,7]. For t>=7, nonnegativity of K_t
alone gives

    C >= B+(9/10)(1+B)/(1-t/30)
      >= B+(27/23)(1+B) > min C.

If t>=30 no source in this class has kappa>0. Thus PT14 is a
continuous optimization, not a grid estimate. The input K table and
complete moment calculation are reused from the independently checked
height-three clipping-envelope artifact.

The statement pays the COMPLETE possible tail by its cylinder maxima.
It does not force an actual finite original inventory to occupy every
height or charge its maximum: keeping actual incidence, common unused
capacity, stronger same-source moments, several clipping levels, or
changing the Q-source may improve the estimate. PT14 is a rigorous
boundary of this source-only scalar envelope, not of all clipped laws
and not of the through-height-three noncoverage class.

[Report579](579-two-root-convex-clipping-has-an-exact-certificate-boundary.md)
allows the two legal roots to have independent clipping thresholds and
weights while keeping one actual joint law. It determines the exact
minimum of that construction's complete two-hinge certificate. The two
certificate minima concern different bounds and do not order the best
actual query norms of the two constructions.

## Verification

[pure_prime_density_query_tradeoff.py](../../frontier/cover-geometry/pure_prime_density_query_tradeoff.py) checks actual comb partitions,
private witnesses, explicit source masses, exact maxima and density
tradeoffs at finite heights. It also exhausts all1120 pure families
with optional originals through height3 and verifies the binary-source
construction, then checks the exact cap and scalar-envelope constants.
The producer completed456 named checks with exit0, using the canonical
`height_three_clipping_envelope.json` as its hinge input. General-prime
comb diagnostics include p=3,5,7, and the telescoping dual coefficients
are checked at p=3,5,7,11 through H=64.
The ordinary proofs above carry the universal quantifiers; the finite
diagnostics do not substitute for them. The exact results are in [pure_prime_density_query_tradeoff.json](../../frontier/cover-geometry/pure_prime_density_query_tradeoff.json).

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_prime_density_query_tradeoff.py

No new Lean verification or external novelty claim is made.
