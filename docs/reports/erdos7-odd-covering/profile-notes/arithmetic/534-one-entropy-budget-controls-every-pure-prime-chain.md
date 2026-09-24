# One entropy budget controls every occupied pure-prime chain

For every actual finite family on P={3,5,7,11,13,17,19}, one law on its
complete survivor controls all labels outside an irredundant original
core, all pure prime powers in that core at arbitrary heights, and all
mixed core labels above10^9, with combined query cost below9.044554.
Only shallow mixed occupied core labels remain in this decomposition,
with sufficient residual budget51863873/25500000>2.033877.

The proof uses the entropy and density of the same
[report530 Gibbs law](530-one-supported-law-controls-unused-and-deep-occupied-labels.md).
A finite cylinder moment inequality pays all seven pure chains jointly,
so a single entropy term cancels. No independent per-prime probability
laws are substituted. This is an ordinary proof and exact rational
arithmetic, not new Lean verification or a resolution of unrestricted
Erdős#7.

## Keep the actual survivor while removing redundant original labels

Let M be the finite set of distinct nonunit P-smooth numerical moduli,
with one globally fixed original cylinder C_d per label. H is Haar
probability on the P-adic product, and U is the survivor of every original.
Choose an inclusion-minimal subfamily M0 whose union is still the full
original union. Its survivor is exactly U.

Every numerical label removed from the original core remains a query
label. It is merely unused relative to M0, so the existing unused-query
bound controls it. No residue of a retained original changes.

Write q_d(nu)=max_a nu([a]_d), and let R_unused refer to the complete
set of nonunit P-smooth labels outside M0, including all query heights.
Put

    alpha=7235955529/6075000000000,
    Lambda=1/alpha,
    rho=H|U/H(U),       D_H(nu)=KL(nu||H).

Report530 with zero replacement gives a nonempty class G of laws on
this same U satisfying

    nu<=Lambda H,
    R_unused(nu)+KL(nu||rho)<=log(H(U)/alpha).

Because nu is supported on U,

    KL(nu||rho)=D_H(nu)+log H(U).

Thus G is equivalently specified by the density bound and

    R_unused(nu)+D_H(nu)<=log Lambda.               (PE1)

All inequalities below use one nu in G. The argument does not require
an infinite Gibbs density formula or a new compactness construction.

## A finite one-prime moment with disjoint forbidden cylinders

Fix p>=3, n>=1 and E subset{1,...,n}. At each occupied depth j in E,
let C_j be an original depth-j cylinder and A_j any query depth-j
cylinder in the same p-adic coordinate. Suppose the C_j are pairwise
disjoint. With e=exp(1), define

    M_(p,n)=sum_(k=0 to n-1)(p-1)*e^k/p^(k+1)
             +e^n/p^n-sum_(j=1 to n)1/p^j.

Then

    integral_(outside union C_j) exp(sum_(j in E)1_Aj) dH_p
       <=M_(p,n).                                  (PE2)

Expand the exponential as a product of1+(e-1)*1_Aj. For nonempty
S subset E, an intersection of its query cylinders has measure at
most p^(-max S). Also the integral of the exponential over the
pairwise disjoint forbidden cylinders is at least their total mass.
Consequently the left side of(PE2) is at most

    1+sum_(nonempty S subset E)(e-1)^|S|*p^(-max S)
       -sum_(j in E)p^(-j).                         (PE3)

Adding a missing depth t increases(PE3) by

    (e-2)*p^(-t)
      +sum_(nonempty S subset E)(e-1)^(|S|+1)
                                  *p^(-max(S union{t}))>0.

Thus the full depth inventory maximizes this bound. For nested query
cylinders A_1,...,A_n, the count equals k on a region of mass
(p-1)/p^(k+1) for0<=k<n and equals n on mass p^(-n). Integrating and
subtracting the forbidden masses gives M_(p,n).

This one-coordinate bound is sharp. Put A_j=[0]_(p^j), C_1=[1]_p,
and C_j=[2+p^(j-1)]_(p^j) for j>=2. All queries lie in root0;
the forbidden cylinders are disjoint in roots1 and2. Every intersection
bound and every removed unit integrand in(PE3) is attained. This proves
sharpness of(PE2); it does not prove optimality of later numerical
cutoffs, entropy estimates or supported laws.

In the actual irredundant M0, pure originals on each prime satisfy the
required disjointness. Two p-power cylinders are disjoint or nested;
a nested smaller cylinder would be redundant in the original core.

## Cancel the entropy once for all seven coordinates

Choose finite cutoffs n_p, and for each occupied p^j with j<=n_p
choose a cylinder A_(p,j) attaining q_(p^j)(nu). All these phases are
chosen under the same nu. Define the finite function

    f(x)=sum_(p in P) sum_(j<=n_p, p^j in M0)1_A(p,j)(x_p).

The actual U lies in the product of the complements of these pure
originals. Mixed original constraints can only shrink U. Therefore

    integral_U exp(f)dH<=product_(p in P)M_(p,n_p).  (PE4)

Only the genuinely independent Haar coordinates are factored here;
no mixed conditional cylinder maxima are multiplied separately.

The classical entropy variational inequality, applied to nu supported
on U, gives

    integral f dnu-D_H(nu)<=log integral_U exp(f)dH.

For completeness, if g=dnu/dH, Jensen applied under nu to exp(f)/g
gives this inequality, since the integral over U of exp(f) is at least
its integral over{g>0}. Density domination makes the entropy finite.
Combining with(PE4) yields

    sum_(p in P)sum_(j<=n_p, p^j in M0)q_(p^j)(nu)-D_H(nu)
       <=sum_(p in P)log M_(p,n_p).

Adding(PE1) cancels the same entropy term:

    R_unused(nu)+sum_(p in P)sum_(j<=n_p,p^j in M0)q_(p^j)(nu)
       <=log Lambda+sum_(p in P)log M_(p,n_p).       (PE5)

This holds for every law in G, not a different law for each chain.

## Explicit all-height query bound

Take B=10^9 and, in the displayed prime order, fix

    (n_3,n_5,n_7,n_11,n_13,n_17,n_19)=(8,7,7,7,7,7,7).

The largest exponents with p^N_p<=B are

    (N_3,N_5,N_7,N_11,N_13,N_17,N_19)=(18,12,10,8,8,7,7).

Let tau_P(B) be the retained sum of1/d over all P-smooth d>B. Remove
its pure powers to obtain the exact mixed reciprocal tail

    tau_mixed(B)=tau_P(B)-sum_(p in P)1/(p^N_p*(p-1)).

The density bound pays the pure powers above n_p and the occupied
mixed labels above B. They are disjoint query classes. Hence

    R_unused(nu)
      +sum_(d in M0, d a pure prime power)q_d(nu)
      +sum_(d in M0, d>B, d mixed)q_d(nu)
    <=log Lambda+sum_p log M_(p,n_p)
         +Lambda*(tau_mixed(B)+sum_p1/(p^n_p*(p-1))).             (PE6)

The fixed rational consumer proves

    log Lambda<53863/8000=6.732875,
    sum_p log M_(p,n_p)<2240699/1000000=2.240699,
    Lambda*(tau_mixed(B)+sum_p1/(p^n_p*(p-1)))
                         <70979023/1000000000=0.070979023.

Their sum is9044553023/1000000000, strictly below

    C=4522277/500000=9.044554.                      (PE7)

No original-height cutoff is assumed. Original pure powers above n_p
are paid by their convergent reciprocal tails, and every original
constraint remains in U. This is a uniform all-height bound for the
stated subset of queries, not a finite-state algorithm.

For the full target T=565/51, the residual budget is

    delta=T-C=51863873/25500000>2.                 (PE8)

It suffices to find one nu in G with

    sum_(d in M0, d<=B, d mixed)q_d(nu)<delta.

The estimate(PE6) already holds for any such nu. A core with at most
two such shallow mixed labels satisfies this sufficient condition, since
each q_d<=1 and delta>2. The general remaining premise is not proved here.

## Full support without claiming entropy preservation

Report467 supplies a law mu for this same actual U with

    (1/5)H|U<=mu<=Lambda H,     R_P(mu)<=70871/3375.

Set epsilon=1/10^7 and nu_hat=(1-epsilon)*nu+epsilon*mu. Convexity of
each query maximum gives

    (1/50000000)H|U<=nu_hat<=Lambda H,

and the combined query contribution in(PE6), now under nu_hat, is below

    (1-epsilon)*C+epsilon*(70871/3375)<9.044556.    (PE9)

The corresponding sufficient residual bound under this same mixed law
is T-9.044556=25931911/12750000. No entropy bound for the mixture is
claimed. A residual estimate for nu is not silently transferred to
nu_hat; it must be paid under whichever law is used for the final target.

## A mixed triple is necessary for a finite dual challenge

Suppose a finite query inventory has fixed phase distributions theta_d,
w_d(x)=theta_(d,x mod d), and sum_d w_d(x)>=T throughout U. Let J be
only its mixed occupied core labels d<=B, and put z(x)=sum_(d in J)w_d(x).
Under a single nu in G, all queries outside J have combined expectation
less than C by(PE6). Therefore

    E_nu z>delta.

For any finite vector w with coordinates in[0,1], let e2(w) and e3(w)
be its elementary symmetric sums of degrees two and three. Pointwise,

    e2(w)>=(2*sum w-3)_+,
    e3(w)>=(sum w-2)_+.

One proof minimizes the multi-affine polynomials e2-2*sum w+3 and
e3-sum w+2 at vertices of the cube. At a vertex with k ones they equal
(k-2)*(k-3)/2 and(k-2)*(k-3)*(k+2)/6, respectively, both nonnegative
for every integer k>=0. The symmetric sums themselves are nonnegative.

Integration and nu<=Lambda H now force the same-phase moment hierarchy

    integral_U z dH>alpha*delta,
    integral_U sum_(d<e in J)w_d*w_e dH>alpha*(2*delta-3),
    integral_U sum_(d<e<g in J)w_d*w_e*w_g dH>alpha*(delta-2)>0.   (PE10)

The exact third threshold is

    alpha*(delta-2)=6250946610703817/154912500000000000000.

Its decimal value lies strictly between0.000040351466864867696280
and0.000040351466864867696281. Expanding(PE10) retains the actual
triple intersections U intersect[a]_d intersect[b]_e intersect[c]_g
and their common weights theta_(d,a)*theta_(e,b)*theta_(g,c).
Thus at least one positively weighted, surviving mixed triple of
shallow occupied core labels is necessary. These tests are not sufficient
for a dual certificate; the pointwise payoff on every actual survivor
still has to hold.

The phase-free reciprocal relaxations sum1/d>alpha*delta,
sum1/lcm(d,e)>alpha*(2*delta-3), and
sum1/lcm(d,e,g)>alpha*(delta-2) are also necessary, with sums over J.
They follow by bounding each compatible cylinder intersection by its
Haar mass1/lcm and summing the fixed phase probabilities. They discard
actual phase compatibility and cannot replace(PE10).

## Exact arithmetic scope

The [consumer](../../frontier/cover-geometry/pure_chain_entropy.py) reads
only the pinned [retained tail](../../frontier/cover-geometry/phase_resampling_arithmetic.json).
Its [result](../../frontier/cover-geometry/pure_chain_entropy.json) contains
the rational moment bounds, density tail and residual budgets. For x>0,
it uses the positive Taylor sum through degree m as a strict lower
bound on exp(x); if x<m+2, adding the first omitted term divided by
1-x/(m+2) gives a strict upper bound. The coefficients of M_(p,n) that
depend on e are positive, so a rational upper bound on e controls their
product. Positive Taylor lower bounds at the proposed logarithm bounds
then certify the two logarithmic comparisons. These computations do
not enumerate original phases or substitute for the general proof above.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pure_chain_entropy.py
```

[Report536](536-ternary-conditioning-preserves-a-joint-query-and-entropy-boundary.md) gives the exact ternary-prefix query and entropy transport for this same G. An actual four-class core shows that fixing a full ternary coordinate need not give a two-copy cofactor family. The conditional kernels must satisfy the global density, entropy and original-label query conditions before they can pay the remaining mixed cost.

[Report535](535-mixed-chain-moments-retain-shared-prime-correlations.md) extends the individual moment to mixed divisibility chains. Two actual chains sharing3 defeat multiplication of those bounds, even at simultaneous maximizing phases of one law in G; the remaining mixed estimate must retain their common prime correlations.
