# Fixed-quota and reciprocal-payment obstructions

The improved denominator from [report531](531-fixed-cardinality-resampling-beyond-the-uniform-leakage-bound.md)
does not enlarge the scalar query certificate's range. Uniform fixed-quota
selection is excluded below; a separate covering inequality also excludes
report530's full reciprocal-density remainder payment for every nonuniform
selection law. Both results concern specified numerical upper certificates,
not the optimal query cost over actual supported laws. The fixed-cardinality
Gibbs theorem remains valid. The general query target and unrestricted
Erdős#7 remain unresolved. These are ordinary proofs, not new Lean verification.

## Fixed-cardinality result and exact scope

Use the actual-family setting and constants of report531:

    P={3,5,7,11,13,17,19},
    A=212731/110592,
    T=565/51,
    alpha=7235955529/6075000000000,
    h=H(U), a=1-h,
    lambda=sum_(d in M)1/d<=A,
    f0=A-lambda>=0.

M is a finite set of distinct nonunit odd P-smooth numerical labels, with one globally fixed original class per label. H is Haar probability, U is the complete original survivor, E_S is the cell covered by exactly the labels in S, N(x) is the original covering multiplicity, and a1=H(N=1). The previous actual-family theorem supplies

    h>=alpha,       log(h/alpha)>=f0.

Select exactly k of the n=|M| labels uniformly, with 1<=k<=n and r=k/n. Its phase-free leakage is

    L_k=sum_(nonempty S subset M)H(E_S)*(k)_(|S|)/(n)_(|S|),

where inclusion is zero if |S|>k. Whenever beta=alpha-L_k>0, define the numerical full-query certificate

    Q_k=[log(h/beta)-(1-r)*f0]/r.

Then Q_k>T for every actual family with h<=A/T. Thus the scalar fixed-cardinality certificate does not enlarge the elementary normalized-Haar regime h>A/T, even though report531's actual two-label example strictly improves the resampling denominator at a fixed marginal weight.

The same obstruction holds when exactly k labels are selected uniformly from any nonempty occupied block C, while D=M minus C is left unweighted and paid with gamma/beta_C, provided

    sum_(d in D)1/d<=gamma<1/80.

No parameter scan, arithmetic realization search or infinite-cardinality limit is needed. The proof uses the actual numerical-label restriction in the singleton-quota case. It does not infer that arbitrary scalar multiplicity data are arithmetically realizable.

## Small survivor mass: h<=1/32

Every singleton covering cell is exposed with probability r, regardless of correlations between selections. Therefore

    a1>=2a-lambda,
    L_k>=r*a1.

Using the actual-family constraint and -log(1-z)>=z,

    Q_k>=f0+L_k/(alpha*r)
       >=f0+(2a-lambda)/alpha
       >=(31/16-A)/alpha
        >38525/3456>T.

This is the same singleton argument as report531(UR4); independent replacement was not needed in this branch.

## Larger h: 1/32<=h<=A/T

The already established rational bounds imply

    a>33/40,
    H(1<=N<=2)>21/80>1/4,
    f0<9/8,
    h/alpha>25.

Here a stronger elementary logarithm comparison is useful:

    exp(5/2)=exp(1)^2*sqrt(exp(1))<9*2=18<25,

using exp(1)<3. Hence log(h/alpha)>5/2, and

    Q_k=[log(h/beta)-f0]/r+f0
        > (11/8)/r.                                (FK1)

### At least two labels selected: k>=2

For n>=k>=2, the inclusion probability of any specified pair satisfies

    p_k(2)=r*(k-1)/(n-1)>=r^2/2.

Indeed n(k-1)/(k(n-1))>=1/2. Singleton inclusion r also exceeds r^2/2. Consequently the positive covered mass with multiplicity at most two gives

    L_k>r^2/8.

Feasibility L_k<alpha<1/800 forces r^2<1/100, hence r<1/10. Substituting into(FK1),

    Q_k>55/4=T+545/204>T.                           (FK2)

This includes k=n whenever its denominator is feasible; the inequalities in fact make feasibility impossible there.

### Exactly one label selected: k=1

If n>=9, then r=1/n and(FK1) gives

    Q_1>99/8=T+529/408>T.                           (FK3)

If n<=8, the numerical original-label restriction supplies the missing information. Sort the distinct odd labels. The smallest is at least3, the second at least5, and every further label is at least7. Padding a smaller inventory to eight for this upper bound gives

    lambda<=1/3+1/5+6/7=146/105<3/2.

Thus

    a1>=2a-lambda>33/20-3/2=3/20,
    L_1=a1/n>3/160>1/800>alpha.

The stipulated positive denominator is impossible. This closes every finite n, including all cases where fixed-cardinality selection suppresses the pair term completely. The bound146/105 is intentionally coarse; no enumeration of original moduli is used.

## One selected block with the stated reciprocal-tail payment

Let n=|C|, 1<=k<=n, r=k/n, and let V be the survivor of only the retained originals D. The exact phase-free leakage is

    L_C=sum_(nonempty S subset C)H(E_S)*p_(n,k)(|S|).

Define beta_C=alpha-L_C>0 and

    Q_C=[log(h/beta_C)-(1-r)*f0]/r+gamma/beta_C.

For h<=1/32, the full-family singleton mass whose label lies in C is at least a1-gamma: every singleton belonging to D lies in the union of D, of mass at most gamma. Thus

    L_C>=r*(a1-gamma),
    Q_C>=f0+(a1-gamma)/alpha+gamma/beta_C
        >=f0+a1/alpha
         >T.

For 1/32<=h<=A/T, remove the D-union from {1<=N<=2}. The remaining mass is

    >21/80-gamma>1/4.

On this region every covering original belongs to C. If k>=2, the same pair inclusion bound yields L_C>r^2/8, and hence(FK2); the nonnegative tail payment can be dropped from a lower bound. If k=1 and n>=9, the same(FK3) applies.

If k=1 and n<=8, let Nc count originals in C on V. Its covered region has mass

    v=H(V minus U)>=a-gamma>33/40-1/80=13/16.

The total Nc multiplicity mass on V is at most sum_(d in C)1/d<3/2 by the same numerical-label bound. Its private mass therefore satisfies

    H({x in V:Nc(x)=1})>=2v-integral_V Nc dH>1/8.

These are precisely the full-family singleton cells belonging to C. Therefore

    L_C=(1/n)*H({x in V:Nc(x)=1})>1/64>alpha,

again excluding a positive denominator. This proves the paid-block result across the entire h<=A/T interval.

Using any certified leakage upper bound ell>=L_C in place of L_C only shrinks the denominator and increases the displayed numerical certificate, so it cannot evade this obstruction.

## Boundary for several blocks

The argument also gives a direct limited corollary. If several independently sampled blocks have positive quotas at least2, let t=min_b(k_b/n_b)>0. Every singleton inclusion is at least t; every pair inclusion is at least t^2/2, whether the pair lies in one block or two. The conservative certificate obtained by reducing all occupied weights to t,

    Q_min=[log(h/beta)-(1-t)*f0]/t,

is therefore>T throughout h<=A/T, by the same small-mass and k>=2 branches. A retained unweighted tail with reciprocal payment gamma/beta and gamma<1/80 is handled in the same way.

This does not close the exact nonuniform weighted query problem. In particular, quota-one blocks can suppress within-block pair leakage, different weights require a specified conversion to the unweighted query target, and payments based on actual U-cylinder geometry remain outside this result. The scalar fixed-k obstruction is a limitation of these numerical sufficient certificates, not a lower bound on the query cost of every supported law.

## The minimum-weight obstruction also allows quota-one pairs

Partition the whole M into independent fixed-cardinality blocks, all with
positive quota. Permit quota-one blocks of size one or two; every larger
block has quota at least two. With t=min_b(k_b/n_b), let Q_min be the
same minimum-weight certificate above. Then Q_min>T throughout h<=A/T.
This includes any number of quota-one pair blocks. This extension has
no unweighted paid tail and concerns this minimum-weight conversion.

For h<=1/32, singleton cells are selected with probability at least t,
so L>=t*H(N=1)>=t*(2a-lambda). The previous small-h argument gives
Q_min>38525/3456>T.

For h>=1/32, call a cell bad when N=2 and its two covering labels form
one quota-one two-label block. Let b be its total Haar mass, m1=H(N=1),
and m2 the mass of the other N=2 cells.

Distinct odd numerical labels d,e satisfy

    H(C_d intersect C_e)<=1/lcm(d,e)<=(1/4)(1/d+1/e).

Indeed d=gu,e=gv with u,v coprime odd integers and u!=v; then u+v>=4,
and the two fractions are1/(guv) and(u+v)/(4guv). Incompatible original
phases only decrease the intersection. Quota-one pairs do not reuse
labels, so summing their intersection bounds gives

    b<=lambda/4.

The actual multiplicity identity and the inequality N>=3 on all other
covered cells give

    2m1+m2 >=3a-lambda-b >=3a-5lambda/4 >3/80,

where a>33/40 and lambda<39/20. Every nonbad pair has inclusion
probability at least t^2/2: inside a quota-at-least-two block this is the
fixed-cardinality pair bound; across blocks it follows by independence.
Singleton inclusion is at least t>=t^2. Therefore

    L >=(t^2/2)*(2m1+m2)>3t^2/160.

Since alpha<1/800, feasibility gives L/alpha>15t^2 and 15t^2<1.
The actual-family large-h inequalities log(h/alpha)>5/2 and f0<9/8
now yield

    Q_min >[11/8-log(1-15t^2)]/t.

Convexity of -log(1-u), using its tangent at u=1/2, gives

    -log(1-u)>=log(2)+2u-1,       0<=u<1.

Also log(2)>2/3; for example integrate the strict convex tangent bound
for1/x at x=3/2 over[1,2]. Consequently

    Q_min >25/(24t)+30t >=5*sqrt(5)>T.

The middle step is AM-GM. The last strict comparison follows from
125*51^2-565^2=5900>0.

## A remaining partition must contain specific actual double-cover cells

Now allow arbitrary positive quotas in the independent blocks, with no
unweighted tail. If Q_min<T, the small-h exclusion first forces h>1/32.
The large-h inequality Q_min>11/(8t) then forces

    t>11/(8T)>1/9.

Every quota-one block therefore has at most eight labels. The preceding
result shows that some such block must have at least three labels.
This can be strengthened to a quantitative condition on its actual cells.
Let b3 be the Haar mass of the N=2 cells whose two covering labels lie
in the same quota-one block of size at least three. Let b2 be the analogous
mass for size-two blocks, and let m2 count all other N=2 cells. The odd-label
intersection estimate still gives b2<=lambda/4. Therefore

    2m1+m2>=3a-lambda-b2-b3>3/80-b3.

If b3<3/80, singleton and good-pair inclusion bounds give

    L>(t^2/2)*(3/80-b3).

Using alpha<1/800, set c=400*(3/80-b3)>0. Feasibility implies
c*t^2<1. The same logarithm tangent and AM-GM argument yields

    Q_min>25/(24t)+2*c*t
          >=5*sqrt(c/3)
           =sqrt((10000/3)*(3/80-b3)).

Hence Q_min<T necessarily implies

    b3>3/80-3*T^2/10000=59/86700.                   (BP1)

The case b3>=3/80 satisfies(BP1) as well. Thus a successful minimum-
weight partition must have actual double-cover cells of total mass
above59/86700 inside quota-one blocks with three to eight labels.
These cells are defined relative to the full original family; a pairwise
intersection covered by a third original is not such a cell. This is a
necessary condition, not an assertion that such a partition or a successful
certificate is realizable. It does not address other weighted conversions.

## Full reciprocal-density remainder payment fails for any selection law

Let K be any random subset of the actual original labels, with a single
law independent of the arithmetic point and query inventory. Set
r_d=Pr(d in K). No independence between labels is needed for the following
covering inequality. Write

    S_x={d in M:x in C_d},
    L=integral_(x outside U)Pr(S_x subset K)dH(x),
    B=sum_(d in M)(1-r_d)/d.

For every nonempty S,

    Pr(S subset K)+sum_(d in S)(1-r_d)>=1.

The complement of {S subset K} is the union of the events {d not in K}.
Integrate this union bound over the original covered region:

    L+B>=1-h=a.                                    (RP1)

Each integral of 1_{x in C_d} equals 1/d. These cylinders all belong to
the same actual original family. L is the phase-free leakage after deleting
the selected originals, before replacement phases can reduce survival.

Suppose the sampling rule has the required inside-survivor domination and
thus supplies the weighted Gibbs budget with beta=alpha-L>0. Paying all
missing query weights using q_d<=1/(beta*d), as in report530(JL7), produces

    Q_pay=log(h/beta)+B/beta.

When h<=A/T<7/40, we have a>33/40>alpha. Consequently

    B/beta>=(a-L)/(alpha-L)>=a/alpha,
    log(h/beta)>=0,
    Q_pay>=a/alpha>660>T.                           (RP2)

The rational comparison follows by multiplying positive denominators;
its excess numerator is L*(a-alpha)>=0. The constant660 uses a>33/40
and alpha<1/800. The logarithm is nonnegative because h>=alpha>=beta.

No choice of nonuniform marginals, dependence or fixed block quotas can
rescue this particular payment in the nontrivial Haar regime. Replacing L
by an upper bound ell>=L only shrinks beta and worsens Q_pay. Inequality
(RP1) also holds for a sampler without the Gibbs inside bound; it does not
grant that bound to arbitrary correlated samplers.

## What the exclusions leave unresolved

The whole-inventory fixed-k conversion, its stated paid block, the minimum-
weight conversion allowing only quota-one blocks of size at most two, and the full
reciprocal-density remainder payment cannot cross T outside h>A/T.
The same-family all-depth query problem is still open.

These exclusions do not treat actual survivor-cylinder payments

    q_d<=min(1,max_a H(U intersect[a]_d)/beta),

phase-dependent exterior leakage, or all conversions of a nonuniform
weighted Gibbs budget. Those estimates must retain the same complete U
and the same query phases throughout. Any remaining minimum-weight route must satisfy(BP1) using quota-one
blocks of size three to eight. Other weighted conversions still need
a valid unweighted query bound that evades the payments excluded here.

Report531's originals0 mod525 and0 mod875 still give a strict improvement
of the sampling denominator. Their h=2618/2625 lies in the already
sufficient uniform-Haar regime, so this does not contradict the exclusions.
The new rational thresholds above follow by the displayed exact arithmetic;
no new parameter scan or Lean proof is used.

[Report533](533-clipped-payments-require-retained-tail-geometry.md)
examines the probability-one truncation min(1,1/(beta*d)). Its scalar
relaxation can pass, but the seven cheapest labels have a sharp actual
survivor bound272/1001. The resulting mandatory retained tail gives a
stronger clipped-cost inequality excluding the entire interval
1/100<=H(U)<=1/10. This still concerns a specified numerical certificate,
not the optimum over actual supported laws.
