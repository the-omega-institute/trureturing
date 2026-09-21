[Index](../../marked_head_profile.md) · [Actual carrier mixture](../001-064/46-one-forbidden-carrier-mixture-strengthens-survival.md) · [Actual source measures](../001-064/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Whole-J source neighborhood](329-a-finite-whole-j-neighborhood-covers-high-surplus.md)

# Irredundant source-seven labels bound the actual surplus

Let a finite family of distinct odd forbidden moduli, all greater than
one, have no original class contained in another original class. Suppose its own effective9
source satisfies

    qJ>=1-delta, 0<=delta<=1/4000.

For the actual source mass S and common-carrier lower mass S0 of46/302,
its surplus obeys

    rho=S-S0 <= 273719/3937640+(2994037/11812920)delta
             <= 469660291/6750240000
              = 0.069576828527578278... < 1/10.       (IR1)

An irredundant family has the required absence of containment, because
every original class has a private integer. In particular, a minimal
subcover of an assumed finite covering family satisfies that premise.
The proof uses only absence of containment between original classes;
it does not require a covering assumption.

Thus no such family, with its OWN source parameters, satisfies the
conjunction `qJ>=1-1/4000` and `rho>=1/10` used in333. Deleting redundant
classes from another family need not preserve its qJ or rho. This is an
ordinary conditional source bound, not a Lean result or a contradiction
to the existence of a covering family.

## High qJ forces five layers of original shallow labels

Use [302's normalized chart](../257-320/302-a-positive-actual-source-neighborhood-keeps-j-below403.md):
the surviving mod9 cells are(0,3,1,4,7), with ROOT=(0,0,1,1,1).
The concentration argument in [71](../065-128/71-global-j-k-control-faces-and-exact-escape-gaps.md)
allows exchanging cells0 and1 so that

    pi_(0,1)>=1-delta,
    deficit0>=(1-delta)/2,
    alpha1>=(1-delta)/4,
    beta2+beta3+beta4>=(1-delta)/4,
    late2+late3+late4>=(1-delta)/72.

The actual carrier definition in46(JC2) is

    pi_c=sum_(e>=1)(6/7^e) 1_(c_e=c).

Here c_e records the actual old root of original3*7^e and old cell of
original9*7^e. An absent label, or an old carrier killed by the fixed3/9
pair, is empty. As302 specifies, a present label's seven-cylinder being
killed by pure7 does NOT make this geometric carrier empty.

If6/7^e>delta, the carrier c_e must equal(0,1): otherwise the weight
missing from pi_(0,1) exceeds delta. Since6/7^5>1/4000, all e=1,...,5
have this carrier. These are actual forbidden labels, not independent
tests or completed labels.

Let A be old root0 and B old cell1, so B is a subset of A. Write P_e
for the seven-cylinder of original3*7^e, and Q_e for that of original
9*7^e. Their old carriers are respectively A and B. Absence of
containment gives the following disjointness facts:

- The five P_e are pairwise disjoint. Any intersection would put the
  deeper cylinder inside the shallower one, and their common old
  cofactor would make the whole deeper original class contained.
- The five Q_e are pairwise disjoint by the same argument.
- P_1 is disjoint from every Q_e. Otherwise the whole original9*7^e
  class would be contained in original21.
- A present pure7 depth-one class is disjoint from all selected P_e
  and Q_e, since it would otherwise contain that mixed original class.

No other cross-family disjointness is assumed. In particular a deeper
P_e may meet a shallower Q_f without either full original class being
contained in the other.

## The same raw old masses remain on both carriers

Use48(SC1)'s actual raw35 survivor measure Lambda and raw pure3 masses:

    eta_i=(1-deficit_i)/9,
    n_i=Lambda(cell i)
       =eta_i*(z-alpha_ROOT(i)-beta_i)-late_i,
    sum deficit<=1/2, sum alpha<=1/4,
    sum beta<=1/4, sum late<=1/72, z>=3/4.

The concentration inequalities imply

    alpha0<=delta/4,
    beta0+beta1<=delta/4,
    late0+late1<=delta/72,
    eta0+eta1>=1/6,
    eta1>=1/9-delta/18, eta_i<=1/9.

Set mA=Lambda(A)=n0+n1 and mB=Lambda(B)=n1. Directly on this actual
source,

    mA >= (1/6)(3/4-delta/4)-(1/9)(delta/4)-delta/72
        =1/8-delta/12,
    mB >= (1/9-delta/18)(3/4-delta/2)-delta/72
        =1/12-delta/9+delta^2/36
        >=1/12-delta/9.                              (IR2)

Both factors in the second product are positive on the stated interval.
Thus the raw35 deletions have not killed either whole carrier. These
lower bounds retain the actual Lambda; they do not enlarge it to a
product measure when estimating deletion from below.

## A shallow bound already forces positive source deletion

Let U7 be the actual pure7 forbidden union, u7 its surviving Haar mass,
and nu7 the normalized actual pure7 survivor law. For either P_1 or Q_1,
no pure7 depth-one cylinder intersects it. There is at most one original
pure7 cylinder at each larger depth, so its remaining Haar width is at
least

    1/7-sum_(h>=2)7^-h=1/7-1/42=5/42.

Its nu7 mass is therefore at least5/(42u7)>=5/42. The21 and63 rectangles
are disjoint, yielding

    s-S >= (5/42)(mA+mB)
         >= (5/42)(5/24-(7/36)delta).                (IR3)

The source identity in48/302 is precisely

    S=(Lambda tensor nu7)(outside the actual mixed7 union),
    s=Lambda(1),
    dmu=1_(full357 survivors) dHaar357/u7.

Thus this is literal actual source deletion. It is not an assigned bad
charge from a clipped physical kernel. Later normalized clipped kernels
do not change this source identity. The entire omitted pure7 exponent
tail has been paid by the geometric sum above.

By46/48, S0>=D=s-C/5. The complete cap estimate in329 is
`C<=1/2+(9/8)delta`. Consequently IR3 alone gives

    rho<=379/5040+(67/270)delta
        <=568969/7560000=0.075260449735449735... .    (IR4)

## Five forced layers retain the pure7 normalization

Put

    a5=sum_(e=1..5)7^-e=(1-7^-5)/6.

On A minus B, the P-family deletes seven width a5. On B, P_1 together
with the Q-family deletes width1/7+a5. These two old-coordinate pieces
are disjoint, so the selected mixed7 union, before pure7 removal, has
raw product mass at least

    D0=mA*a5+mB/7.                                  (IR5)

Let g(y) be its old Lambda mass at a fixed seven-coordinate y. Its whole
old carrier lies inside A; hence0<=g(y)<=mA and integral g>=D0. Also
D0<=mA because mB<=mA and a5+1/7<1.

Let a in{0,1/7} be the Haar mass of the present pure7 depth-one cylinder,
or zero when absent. This cylinder misses all selected mixed labels.
Let x be the Haar mass of the rest of U7 OUTSIDE that first cylinder.
Then

    0<=x<=sum_(h>=2)7^-h=1/42, u7=1-a-x.

Removing that remainder loses at most mA*x from integral g. Therefore,
on the same actual pure7 normalization,

    s-S >= (D0-mA*x)/(1-a-x).

The numerator is positive throughout this rectangle: D0>=mA*a5 and
mA>0, while a5>1/42. The ratio increases with a. At a=0, its derivative
in x is `(D0-mA)/(1-x)^2<=0`. Thus its minimum over the containing
rectangle occurs at a=0,x=1/42, and

    s-S >= [(6-7^-4)*mA+6*mB]/41.                   (IR6)

This bound pays every deeper pure7 cylinder and keeps the actual u7.
It asserts neither that the minimizing rectangle endpoint is realizable
nor that the constant is sharp. Additional mixed7 labels can only enlarge
the actual deleted union.

Both coefficients in IR6 are positive. Inserting IR2 gives

    s-S >= 24009/787528-(33613/1181292)delta.

Finally, using the same established cap C and S0>=s-C/5,

    rho=S-S0 <= C/5-(s-S)
        <=273719/3937640+(2994037/11812920)delta,

which proves IR1. The five selected mixed layers and the complete pure7
tail remain present throughout. The high-qJ region with smaller rho,
and all other source charts, remain unclosed by this result.

## The remaining source region contains an actual irredundant benchmark

The existing N=12 finite source in329 already lies in the remaining
region. Keep all its204 original classes:311's literal raw35 classes,
pure7 cylinders G_(6,e), and mixed3*7^e and9*7^e cylinders G_(1,e)
and G_(2,e), respectively, for1<=e<=12. Here
G_(j,e)=[j*7^(e-1)] mod7^e; the old carriers remain root0 and cell1.

Pairwise noncontainment alone would not establish irredundancy relative
to the union of all other classes. The
[benchmark helper](../../frontier/source-budgets/irredundant_whole_j_finite_source.py)
constructs a private integer for EACH of the204 original classes and
directly checks that integer modulo ALL204 original moduli. Every
integer belongs to its designated class and avoids the other203.
Thus every class is necessary to this family's forbidden union.

The finite prefix partitions are used to find candidates: the raw35
search visits all49*49 leaf pairs, with seven coordinate fixed at3.
Those leaves partition the raw35 coordinates for original-label
membership. Seven-ending classes use the surviving old point(3,2).
The final41616 direct modular checks, independently of the search
partition, certify the private-witness property. An additional integer
avoids all204 classes, so this irredundant family is NOT a cover.

Exact reconstruction agrees with329's existing mass calculation:
delta=1-qJ=0.00003388634450980418...<1/4000 and
rho=0.05833338038722376..., below the same-delta IR1 upper
0.0695220535624771... . This supplies an actual benchmark within the
remaining region; it asserts no extremality or later-prime coverage.
The [certificate](../../certificates/source_norms/source-budgets/irredundant_whole_j_finite_source.json)
retains every original label, private integer, search partition and
exact mass, and binds this proof and the311/329 construction sources.
The helper supports external working directories and explicit
`--base`, `--proof`, `--certificate` paths; no Lean result is asserted.

## Forced source deletion gives a nonempty source guard through37

Suppose the same original family also contains a class of modulus7.
There is positive actual survivor mass after all its original classes
whose largest prime is at most37 whenever

    qJ>=1-1/4000, rho>=7/125.                              (IR7)

The fixed physical chain below gives normalized survivor mass greater
than1/1000 after37. Consequently an original family in this source guard
with all prime factors at most37 cannot cover the integers. Original
exponent heights remain unrestricted. The existing N=12 benchmark
satisfies the guard, so the source domain is nonempty. The benchmark is
itself a noncover; no existence of a covering system is asserted.

### One actual source and its pointwise deletion

Work in the actual effective9 chart of329, with
`qJ>=1-delta`, `0<=delta<=delta0=1/4000`, no original class contained in
another, and an original class of modulus7. The modulus7 requirement
means depth one; a class with modulus7^e at a deeper level alone does not
supply it. An extremal cover as in[350](350-extremal-paired-branch-and-source-support.md)
supplies this requirement by divisor closure when its period has prime7,
and supplies noncontainment by irredundancy. The actual chart and qJ
requirements remain explicit restrictions.

Keep the actual raw35 survivor measure Lambda, raw pure3 measure eta,
normalized actual pure7 survivor law nu7, and actual mixed7 union Bmix:

    dmu=1_(Bmix complement) d(Lambda tensor nu7),
    S=mu(1), s=Lambda(1), rho=S-S0.

Use the old root A and its distinguished cell B from the five-layer
argument above. With surviving cells(0,3,1,4,7), put

    a=(6-7^-4)/35, b=6/35,
    zeta=(a,a+b,0,0,0), w_l=1-zeta_l.

The old35 marginal of mu obeys the pointwise measure bound

    mu35 <= w Lambda <= w(eta tensor Haar5).             (IR8)

Indeed the forced mixed widths are at least
`a5=sum_(e=1..5)7^-e` on A minus B and `a5+1/7` on B.
The actual modulus7 cylinder has width1/7 and misses every selected
mixed cylinder. The remaining pure7 union outside it has width
`x<=1/42`. For either mixed width d, the deleted fraction is at least
`(d-x)/(6/7-x)`. This decreases with x because `d<6/7`; at x=1/42 the
two bounds are a and a+b. Additional mixed labels enlarge the deleted
union. All these statements concern the same original coordinates.

Integrating(IR8) against Lambda and using(IR2) gives the useful necessary
bound

    s-S >= a*mA+b*mB,
    rho <= (18+7^-4)/280+[(217-2*7^-4)/840]delta
         <=14832829/230496000=0.06435178484659... .       (IR9)

This strengthens(IR1) only under the original modulus7 premise.

### The same original zero7 block carries the nonlinear gain

Let `h_t(v)=(v-t)_+` for rational t>=1. In a complete original357 test L,
let A0 be its own zero7 block. It is a complete original35 load, including
its unit. Monotonicity gives

    integral h_t(L) dmu
      = integral h_t(A0) dmu
        + integral [h_t(L)-h_t(A0)] dmu
      <= integral w*h_t(A0) dLambda
        + integral [h_t(L)-h_t(A0)] d(Lambda tensor nu7).
                                                               (IR10)

Apply[31's original-label comparison](../001-064/31-one-original-zero-five-layout-across-both-actual-measures.md)
and centered Jensen to the second term before taking any supremum. Set

    p1=29/35, p_n=36/(5*7^n) for n>=2,
    Q_t(v)=sum_(n>=1)(p_n/n)[h_t(nv)-h_t(n)],
    G_(t,l)(v)=Q_t(v)-zeta_l*h_t(v).                       (IR11)

Only the zero7 block's cell cost changes. Every positive7 block keeps
its previous complete centered cost. The cost G_l is nonnegative,
increasing and convex, and G_l(1)=0: its h_t coefficient is
`p1-zeta_l>=(17+7^-4)/35>0`; every remaining term in(IR11) has a
nonnegative coefficient. Its eventual slope is1-zeta_l, retained
separately in each cell.

Let F_theta be[42's cell-dependent raw35 operator(A2)](../001-064/42-whole-hinge-absorption-sharpens-actual-survival.md).
Writing B_t(theta) for the existing raw357 hinge upper, define

    Bnew_t(theta)=F_theta(G_(t,l))
                      +[B_t(theta)-F_theta(Q_t)].          (IR12)

The bracket is the explicit nonnegative sum of the remaining original7
blocks and the constant term. Formula(IR12) follows from(IR10) on one
original A0. The comparison does not subtract an independently optimized
deleted mass from another test's upper bound.

For completeness,42's deep allocation bound still applies. With actual
old5 availability d_l>=1/4 and its centered5 correction barG_l,

    d_l G_l+barG_l
       =(d_l-1/5)G_l
         +sum_(n>=2)[4/(n*5^n)]*[G_l(nv)-G_l(n)]

is increasing and convex. Both barG_l and its increments are nonnegative.
Thus42(A3)--(A4) bounds arbitrary original ternary-depth schedules. The
complete3,5 and7 tails are summed after their proved affine entrance;
no original depth cutoff or common-residue assumption is introduced.

Let `lambda=1+7delta0`, and let theta* be329's containing whole-face point.
The WF3 pointwise bounds on actual cell masses, pure masses and
availabilities apply to these fixed nonnegative costs. For example,

    d_actual Delta G+Delta barG
       <=lambda[d_star Delta G+Delta barG].

The initial terms and all positive-block terms have the same domination.
Consequently

    integral h_t(L) dmu <=lambda Bnew_t(theta*).           (IR13)

The operator remains separately convex in the original parameter blocks.
The nine vertices with beta and late independently concentrated in a
root1 cell therefore control theta*. This proves finite-delta domination
for the new operator itself, including any fixed nonnegative combination
of its hinge costs.

### A complete weighted cofactor sum supplies the affine tail

Write n_l=Lambda(cell l), eta_l=eta(cell l), and let R(v) be the larger
of the two root sums. Coordinate products below are pointwise. Every
complete original35 nonunit test has weighted cap

    Cw(theta)=R(wn)+max(wn)+max(wd)/18
               +[sum(w eta)+R(w eta)+max(w eta)]/4
               +max(w)/72.                               (IR14)

To see this, its pure3 depth-one and depth-two tests contribute at most
R(wn) and max(wn). The complete deeper3 tail contributes max(wd)/18.
At positive5 depths, the complete weights sum to1/4; the old pure3 unit,
root and cell give the bracket. The deeper3 tail at those depths gives
max(w)/72. Each class keeps its own arbitrary residue. These are upper
bounds for the same weighted source, not separately attainable choices
asserted to coexist.

At all nine containing vertices,

    Cw*=685487/1512630,
    Bnew_1(theta*)=Cw*+3/20.                              (IR15)

The first identity is an exact rational evaluation of(IR14); the second
also follows by evaluating the complete nonlinear operator at h1.
WF3 gives Cw(actual)<=lambda Cw*. The positive7 classes retain the
unchanged cap(s+C)/5, where329 gives
`s<=1/4+delta/2` and `C<=1/2+9delta/8`. Hence

    integral (L-1) dmu <=Cw(actual)+(s+C)/5
       <=lambda Cw*+3/20+(13/40)delta0
       =2923852811/4840416000
       =0.6040499021158512... =: Mw.                      (IR16)

This is the h1 comparison with its finite error split more precisely.
It replaces the earlier complete mean in affine tails; it is not an
additional deletion credit on top of the same weighted cofactor sum.

### A full-Haar11/13 head and one conditioning

Use the following fixed thresholds. At prime p set the clipping
parameter to t/(p-1), full count cap to c_p=(p-1)/(p-1-t), and charge
factor to k_p=1/(p-1-t).

| Prime p | t | c_p | k_p |
| --- | ---: | ---: | ---: |
| 11 | 3 | 10/7 | 1/7 |
| 13 | 4 | 3/2 | 1/8 |
| 17 | 6 | 8/5 | 1/10 |
| 19 | 8 | 9/5 | 1/10 |
| 23 | 9 | 22/13 | 1/13 |
| 29 | 12 | 7/4 | 1/16 |
| 31 | 16 | 15/7 | 1/14 |
| 37 | 20 | 9/4 | 1/16 |

All clipping parameters t/(p-1) lie in(0,1), and all caps are at most p.
[16(SI3)--(SI4)](../001-064/16-a-common-dual-test-law-for-redistributing-charged-bad-mass.md)
therefore supplies normalized full-Haar kernels with the displayed
caps. Pure p-power originals belong to the actual bad union and are
paid by the unit in each complete old-cofactor test. Completing absent
labels in the upper comparison preserves every existing residue.

Let N11 be the complete comparison count with cap10/7, and write
`u_n=Pr(N11=n)` for n<4,
`T0=Pr(N11>=4)`, `T1=E[N11;N11>=4]`, `h=T1-4*T0`.
For each source vertex theta put

    C13(theta)=lambda sum_(n<4)u_n*n*Bnew_(4/n)(theta)+T1*Mw,
    e=1-h/8,
    D=max_theta[lambda Bnew_3(theta)/7+C13(theta)/8].
                                                               (IR17)

Every displayed source hinge has the same value at all nine vertices;
the certificate checks this before replacing the expression by its
maximum. It is equality of comparison values, not a common optimizer.
The11 charge is at most `lambda Bnew_3/(7S)`, and the13 charge, paid
under its own full incoming11 law, is at most `(C13+hS)/(8S)`.
The unnormalized mass z surviving both head primes consequently obeys

    z>=E(S):=e*S-D,
    e=74535/74536,
    D=315424555117789/3758179656000000.                    (IR18)

Normalize once on these actual head survivors. This builds a new head
from its own two physical kernels; no old(4,5) head, J403 guard or earlier
AP denominator is substituted into(IR18).

### Complete continuation and the quantitative guard

For a later row p,t let Z be the product of all post13 comparison
counts from earlier rows, and W=N11*N13*Z. The comparison factors have
probabilities `Pr(N=1)=1-c_p/p` and
`Pr(N=n)=c_p*(p-1)/p^n` for n>=2. Keep the complete product atoms u_n
for n<t, its exact tail T0,T1, and put

    C_p=lambda max_theta sum_(n<t)u_n*n*Bnew_(t/n)(theta)+T1*Mw,
    c_p'=T1-t*T0, f_p=E[(Z-t)_+].                         (IR19)

These auxiliary counts are comparison laws. They are not assumed to be
independent actual forbidden events. Their complete tails pay the entire
n>=t part. Every actual original test retains its own residues.

Each complete original through13 block is at least1. Its post13 hinge
functional Phi is therefore pointwise at least f_p. If z is the actual
unnormalized head survivor mass, removing the killed head gives

    integral Phi d(head survivors)
       <=f_p*z+C_p+(c_p'-f_p)*S.

Since `W>=Z` in the auxiliary product coupling,
`c_p'>=f_p>=0`; also C_p>=0. After the single head normalization,

    H_(<p,t)<=f_p+[C_p+(c_p'-f_p)*S]/(e*S-D).            (IR20)

All later charges are paid under their actual full incoming physical
laws as in331/333. Dropping earlier killed sets only increases their
nonnegative charge integrals. For q in the chain put

    Fq=sum_(17<=p<=q)k_p*f_p,
    Kq=sum_(17<=p<=q)k_p*(c_p'-f_p), Cq=sum_(17<=p<=q)k_p*C_p,
    Aq=(1-Fq)*e-Kq, Bq=(1-Fq)*D+Cq.

Then the actual killed mass after q has normalized lower bound

    eta_(<=q)(1)>=(Aq*S-Bq)/(e*S-D),
    S>=3/20+rho-(263/360)delta0.                         (IR21)

The exact certificate verifies Aq>0 and e*Bq-Aq*D>0 for every row.
Thus(IR21) increases with S. At rho=7/125 its denominator is positive:

    Smin=296377/1440000,
    E(Smin)=1832254746977719/15032718624000000>0.

At q=37, exact rational arithmetic gives

    eta_(<=37)(1)>=0.0013763466468406615...>1/1000.        (IR22)

The exact fractions, rather than rounded decimals, certify both strict
comparisons. This proves(IR7). The corresponding strict positive-mass
threshold is rho>0.05583200732400275914... . At the benchmark limiting
rho=7/120 the37 lower bound is0.0201081639188282... .

The actual N=12 source above has
`rho=0.05833338038722376...>7/125` and
`delta=0.0000338863445098...<1/4000`, and contains an original modulus7
class. Its204 private witnesses give the noncontainment premise. Its
modulus set is already closed under divisors greater than one:

    {3^a*5^b : 0<=a,b<=N, a+b>0}
      union {7^e,3*7^e,9*7^e : 1<=e<=N}.

Adding divisor closure alone therefore does not remove this source
region. The certificate checks the actual finite benchmark against the
new guard. It makes no assumption that it extends to a whole cover.

For comparison, using Mw with the previous supported13 head and the
fixed later thresholds(6,8,9,12,16,18) gives a37 threshold
0.05877996307871... and negative benchmark lower bound
-0.00333634923635... . Under that same old head, the331 and333 reference
chains have thresholds0.06263664078192... and0.06083487104142... .
The new head and its own full count caps are thus part of the proof of
(IR22). No global optimality claim is made. Continuing beyond37, the
other source charts and unrestricted Erdős#7 remain unresolved here.

### Exact verification artifacts

The[source-cost producer](../../frontier/source-budgets/source_own_test_consumer.py)
and its[canonical certificate](../../certificates/source_norms/source-budgets/source_own_test_consumer.json)
retain(IR14), the fixed head and full chain, their complete rational
hinge costs at all nine vertices, the exact guard and benchmark checks,
and the earlier supported-head comparisons. The producer reconstructs
every full product distribution and the post13-only floor, independently
checks the existing product-tail implementation, and pays all affine
tails. Every check remains active under Python optimization.

From the repository root, replay with

    python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/source_own_test_consumer.py --check

The producer pins its inputs, ordinary proof and own bytes. These finite
exact checks do not machine-prove the ordinary source domination or
unbounded exponent arguments. No new Lean result is asserted.

## The complete source mean has the sharp near-J limit38/63

For the actual-source interface above, the best uniform complete nonunit mean tends to38/63 as the qJ neighborhood shrinks to1. The upper bound applies to arbitrary finite own tests; a new sequence of finite irredundant sources and one finite complete test on each supplies the matching lower limit. This is an ordinary asymptotic sharpness theorem.

### Uniform upper bound with any number of forced layers

Let one actual finite distinct-odd original family have no original AP contained in another, an original numerical modulus7, and its own effective9 source with qJ>=1-delta. Retain exactly report339's unnormalized mu, Lambda, normalized pure7 law nu7, and complete original357 own tests L, whose unit is1. For integer K>=5 assume

    0<=delta<=1/4000, delta<6/7^K.

The carrier concentration forces all original3*7^e and9*7^e, e<=K, to have the same old root A and cell B subset A. Replace5 byK in339's disjointness argument. The same pure7 normalization and complete remainder x<=1/42 give

    mu35<=w_K Lambda,
    w_K=1-a_K1_A-b1_B,
    a_K=(6-7^(1-K))/35, b=6/35.

Every remaining original7 height is retained. The K selected layers only prove a lower deletion bound; this is not a depth truncation of the original family or own tests.

At each of the existing nine whole-face vertices, the weighted35 complete nonunit cap in339(IR14) is

    Cw_K=17/36-a_K/12-b/36
         =571/1260+7^(1-K)/420.

To check the max terms: R(wn)=1/8, max(wn)=1/18, max(wd)=(3/4)(1-a_K), sum(w eta)=1/2-a_K/6-b/9, R(w eta)=1/3, max(w eta)=1/9 and max(w)=1. Beta and late may occupy the same or different root1 cells; at least one of the three cells is free of both, attaining the displayed unweighted maximum. The root0 candidates are no larger for K>=5. More explicitly, write x=7^(1-K) in[0,7^-4]. Each candidate difference from the displayed dominant value is affine in x. At x=0 and x=7^-4 the inequalities hold for all nine vertices, so affine interpolation proves them throughout this interval. The root1 root sum, a cell free of both beta and late, and the root0 availability supply the claimed attaining candidates.

Apply the same nonnegative WF comparison to this weighted cap, and the unchanged positive7 cap(s+C)/5 from339. On the same actual source,

    integral(L-1)dmu
      <=(1+7delta)[571/1260+7^(1-K)/420]+3/20+13delta/40.  (U)

Consequently, for sequences of such families with delta->0 and any own tests, limsup integral(L-1)dmu<=38/63. All periods remain finite but may grow. When delta>0, choose K to be the largest integer with delta<6/7^K; for sufficiently small delta it is at least5 and tends to infinity. If delta=0, the same bound holds for every K and one lets K tend to infinity. No finite family with qJ exactly1 is required for the limiting assertion.

### One actual family and one complete test attain the limiting constant

The new family F_N has the same numerical modulus inventory as the earlier benchmark, with the following different residues. For each N>=3 let primes be3,5,7, all original exponents bounded byN. Specify actual CRT residues as follows; unspecified coordinates are absent from that modulus.

* Pure3^a: residue2 for a=1,6 for a=2,3^(a-1) for a>=3.
* Pure5^b: residue5^(b-1).
* Original3*5^b: old3 residue1, old5 residue2*5^(b-1).
* Original9*5^b: old3 residue1, old5 residue3*5^(b-1).
* Original3^a*5^b, a>=3: old3 residue7+3^(a-1), old5 residue3*5^(b-1).
* Pure7: residue6. Pure7^e, e>=2: residue1+7^(e-1).
* P1, original3*7: old3 residue0, old7 residue1. P_e, original3*7^e,e>=2: old3 residue0, old7 residue2+7^(e-1).
* Q1, original9*7: old3 residue3, old7 residue2. Q_e, original9*7^e,e>=2: old3 residue3, old7 residue3*7^(e-1).

There are N^2+5N original moduli, all distinct and odd. The coordinates(4,4,4) avoid all originals, so these are explicit noncovers. Noncoverage does not detract from their role as actual sources attaining the uniform mean limit.

Actual irredundancy can be verified uniformly: use seven coordinate4 for every raw35 label, and five coordinate4 for every pure3 or seven-ending label. The mixed35 rectangles are mutually disjoint and miss every pure3/pure5 AP, by their first-exit3/5 patterns. A pure3 label is private at its own residue with five4/seven4; a pure5 label is private at three4, its own residue, seven4. Each mixed35 label is private at its own two residues/seven4. A pure7 label is private at three4/five4 and its own seven residue. P_e is private at three0/five4/its own seven residue; Q_e at three3/five4/its own seven residue. The original7 pure classes are mutually disjoint. Deeper P_e lie in Q1's seven cylinder but their private three coordinate0 avoids Q1's old cell; deeper pure7 lie in P1's seven cylinder but their private three coordinate4 avoids P1's old root. These are actual private integers by finite CRT, not just numerical noncontainment.

Put

    t=sum_(a=3..N)3^-a, q=sum_(b=1..N)5^-b,
    r=sum_(e=1..N)7^-e, z=1-q, u=1-r,
    a=1/(7u), wA=1-a, wB=1-2a.

For the five surviving mod9 cells(0,3,1,4,7), the actual pure3 masses are

    eta=(1/9-t,1/9,1/9,1/9,1/9),

Here n_j denotes the literal residue j modulo9, with nB denoting residue3. The raw35 masses are

    n0=z(1/9-t), nB=z/9,
    n1=(1-3q)/9, n4=(1-2q)/9,
    n7=(1-2q)/9-tq.

In particular s=sum n=5/9-t-q and R=n1+n4+n7=1/3-7q/9-tq. This has alpha concentrated at root1, beta at cell1 and late at cell7, with late mass tq. Its actual source concentration is

    qJ=(18t)^2(4q)^4(1-7^-N) ->1.

The pure7 deeper tail has width r-1/7 and lies within P1. The P_e,e>=2, are disjoint and lie within Q1. The Q_e are mutually disjoint and all miss P1. Thus the mixed7 union deletes exactly width1/7 from A minus B after pure7 removal and exactly2/7 from B. Therefore on the actual normalized pure7 source,

    mu35=wA Lambda|_(A minus B)+wB Lambda|_B+Lambda|_(A complement).

There is also an entirely untouched seven root4. The latter identity is about the old35 marginal; no domination of the full joint source by this marginal weight is asserted.

Choose a single complete own test L_N on divisors3^i5^j7^k,0<=i,j,k<=N, as follows.

For k=0: at j=0 use three residue1 when i=1,4 when i=2,18 when i>=3. At every j>=1 use five residue4, and use three residue1 if i=1,4 if i>=2 (no three condition if i=0). Include the unit exactly once.

For k>=1 always use seven residue4; use the same raw35 tests except at i=2,j=0, where use three residue3. Each divisor chooses one fixed own-test residue; the test APs are auxiliary observations and are not claimed to belong to the original forbidden family.

The five cylinder4 misses every original pure5 and mixed35 condition. Three cylinder18 at depth>=3 misses all original pure3 and mixed35 conditions, lies in A minus B, and has Haar mass3^-i. Three cylinder4 at depth>=2 is free of all pure3 conditions and lies outside A. These facts give the exact finite k=0 nonunit mean

    V0_N=R+n4+wA*z*t
            +q*[wA(1/9-t)+wB/9+1/3+1/3+1/9+t].       (L0)

The raw35 test used when k>=1 has exact nonunit mean

    C_N=R+z/9+z*t+q.

Seven root4 is entirely free, so the full positive7 mean of this same complete test is exactly

    Vplus_N=(r/u)(s+C_N).                               (L+)

Thus integral(L_N-1)dmu=V0_N+Vplus_N. As N->infinity,

    t->1/18, q->1/4, r->1/6, u->5/6,
    wA->29/35, wB->23/35,
    V0_N->571/1260, C_N->1/2, s->1/4,
    Vplus_N->3/20,
    integral(L_N-1)dmu->38/63.                          (L)

Together(U) and(L) prove the sharp limiting uniform complete nonunit mean for this near-J, original7, noncontained source interface. The test remains finite at each N. The theorem says that no uniform mean constant strictly below38/63 can hold throughout sufficiently small positive qJ neighborhoods. It does not claim a finite extremizer, sharpness of nonlinear hinge costs, sharpness at fixed delta=1/4000, or a contradiction to an odd covering family. Any further continuation argument needing a smaller limiting scalar must strengthen the source hypotheses or use information beyond this uniform complete mean.

### Exact finite verification

The [sharpness producer](../../frontier/source-budgets/source_mean_sharpness.py)
and its [canonical certificate](../../certificates/source_norms/source-budgets/source_mean_sharpness.json)
retain the original CRT classes and a private integer for every class,
the actual old35 and seven partitions, every selected old35 test
integral, all finite positive7 test cylinders, and the exact comparison
with(L0)--(L+). The certificate also retains the eighteen endpoint
vertices that verify the affine max comparisons in(U). No search or
finite optimizer claim is part of this result.

| N | Original classes | Private membership checks | Finite complete nonunit mean |
| --- | ---: | ---: | ---: |
| 3 | 24 | 576 | 0.5974545454545454... |
| 12 | 204 | 41616 | 0.6031743078274497... |
| 24 | 696 | 484416 | 0.6031746031740468... |

The N=3 check verifies the same exact construction outside the small-delta
guard. At N=12 the actual parameters satisfy
`delta=0.0000338863445098...` and `rho=0.0642857815054542...`;
this new finite source is also inside(IR7). These finite checks support
the explicit formulas; the uniform upper and the limit are established
by the preceding arbitrary-K and arbitrary-N arguments.

From the repository root, replay with

    python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/source_mean_sharpness.py --check

The exact fractions in the certificate govern the displayed decimals.
The source family and test are finite for each N, and the test contains
exactly one class for each divisor of105^N, including its unit once.
The theorem concerns the asymptotic uniform complete mean; fixed-delta
optimality, nonlinear hinge sharpness and unrestricted Erdős#7 remain
unresolved. No new Lean result is asserted.

## The actual near-J sources cannot attain their entrywise square envelopes

The same finite family F_N also supplies a strict loss between its actual
square maximum and the sum of independently maximized pair masses. This
is a concrete application of[28's saturation criterion(LCZ4)](../001-064/28-zero-local-losses-do-not-imply-a-common-maximizing-original-layout.md#5-exact-saturation-and-why-this-is-not-a-counterexample-to-full-arc-consistency)
inside the source family above. F12 satisfies the current near-J guard;
F3, although used below to check the formulas, is outside that guard.
No uniform loss for all sources in the guard is asserted.

Put Q_N=105^N. For a finite positive measure m on this actual period, set

    c_m(d)=max_b m(x=b mod d),
    E_N(m)=sum_(d,e|Q_N)c_m(lcm(d,e)),
    Gamma_Q_N(m)=max_layout integral L^2 dm.

Every test retains one independent residue at every divisor, including
its unit. CRT bounds each ordered square term by the displayed cap.
The five terms(1,d),(d,1),(d,d),(d,e),(e,d), for d|e and 1<d<e,
share the same d-residue. If

    A_j=m(x=j mod d),
    B_j=max_(b=j mod d)m(x=b mod e),

their total is at most max_j(3A_j+2B_j). Consequently the same-law
entrywise envelope has the valid local correction

    kappa=3max A+2max B-max_j(3A_j+2B_j),
    Gamma_Q_N(m)<=E_N(m)-kappa.                         (PG1)

This retains near-maximal choices as well as maximizers. Every other
ordered-term loss is nonnegative. The correction includes the diagonal
term(d,d) exactly once; no factor is borrowed from another estimate.

### The original actual source has incompatible mod9 and mod63 maxima

Retain t,q,u,z,a and the raw35 masses n of the F_N construction. Subscripts
in this paragraph are literal residues modulo9; n3 is the earlier nB.
The actual unnormalized mod9 masses are

    alpha=((1-a)n0,(1-2a)n3,n1,n4,n7), S=sum alpha.

For each surviving cell j, the exact largest mod63 subcylinder is

    beta_j=max_(b=j mod9)mu(x=b mod63)=n_j/(7u).         (PG2)

The upper follows from mu<=Lambda tensor Haar7/u. The same seven root4
misses every original seven restriction and attains this cap in every
cell. Thus PG2 concerns the full joint actual source, not a product
substitution for its old marginal.

For every N>=3,

    1/27<=t<1/18, 31/125<=q<1/4, 1/6<a<6/35.

The unique maxima of alpha and beta are respectively at cells4 and3.
Indeed n3 exceeds all other raw masses, alpha4-alpha3=[2a(1-q)-q]/9>0,
alpha0<=94/2025<1/18<alpha4, and alpha1,alpha7<alpha4.
For gamma_j=3alpha_j+2beta_j, its unique maximum is at3: the other
root1 cells are dominated by4, while

    gamma3-gamma0=z[(3-a)t-a/3]>0,
    gamma3-gamma4=[q(21u+8)-6]/(63u)>0.

The first bracket is at least1/21 on the containing box. The second
numerator is greater than81/250, using u>5/6. Applying PG1 with d=9,e=63
therefore gives

    kappa_N=3(alpha4-alpha3)>0,
    Gamma_Q_N(mu/S)<=(E_N(mu)-kappa_N)/S.               (PG3)

At N=12 the exact values are

    kappa12=20114411648143778/8448051270263671875,
    kappa12/S12=593867946705620973561/53448309681763197033148
              =0.0111110706819649... .

As N tends to infinity, kappa_N tends to1/420 and S to3/14, so the
normalized gap tends to1/90. The mean-sharpness construction above does
not supply a layout saturating this square envelope.

### The fixed reweighted source has a different shared-label conflict

Use precisely RW1's cell weights r=(11/8,5/4,1,1,1), and put
m=mu_r=r*mu, T=mu_r(1). Write v_j=r_j*alpha_j. In PG1 now take d=3,e=9:

    A0=v0+v3, A1=v1+v4+v7, A2=0,
    B0=max(v0,v3), B1=max(v1,v4,v7), B2=0.

Here B0=v3 and B1=v4 for all N>=3. The root0 comparison follows from

    (v3-v0)/z=-(1+9a)/72+11(1-a)t/8>=13/1890>0;

the root1 comparison is inherited from alpha. Set

    DeltaA=A1-A0
      =1/3-7q/9-z(21-31a)/72+t[11(1-a)z/8-q],
    DeltaB=B0-B1=5(1-2a)z/36-(1-2q)/9.

For N>=4 use t>=4/81. On the containing box, DeltaA increases with t
and a and decreases with q. For example, its three derivatives obey
`partial_t>=677/1120`, `partial_a>=17/64`, `partial_q<=-241/432`.
Thus DeltaA>=DeltaA(4/81,1/4,1/6)=7/1728>0. DeltaB increases with q
and decreases with a, giving DeltaB>=199/15750>0 at q=31/125,a=6/35.
Both maxima are therefore unique and lie at different roots. PG1 yields

    kappa_r,N=min(3DeltaA,2DeltaB)>0 for N>=4,
    Gamma_Q_N(mu_r/T)<=(E_N(mu_r)-kappa_r,N)/T.          (PG4)

At N=3 both individual maxima lie in root0 and this cluster's gap is
exactly zero. No claim of a common cluster-maximizing root for all N
is needed. At N=12, the second branch of PG4 is the smaller one and

    kappa_r,12=435812164190143141/16896102540527343750,
    kappa_r,12/T12=25734272483263762332909/240369043020445468666057
                 =0.1070615090857388... .

In the limit, DeltaA tends to61/6720 and DeltaB to13/1008. Hence
kappa_r,N tends to13/504, T to1619/6720, and the normalized gap to520/4857.
These are the actual cell weights and the same forbidden sets as RW1;
the mod9/mod63 maximizer argument for mu was not transferred to mu_r.

The existing sharpness producer records the cell masses, cluster
maximizers and exact gaps at its verification heights, as well as these
limits. It reuses the source reconstruction and private-witness checks
above. The arbitrary-N claims follow from the displayed box arguments,
not from a finite scan. This cluster calculation supplies no complete
Gamma value; (FS1) and (FS7) below separately close both F12 maxima.
For tests at a larger complete height H>=N, the same
five terms retain this loss only after E_N is replaced by the matching
larger-height envelope E_H on the Haar lift of the same actual source.

PG3 and PG4 are counterexamples to saturation of these entrywise
envelopes on the current actual sources. RW5/RW10 and the assigned
square bounds use different WF/A2/Jensen expressions; no comparison
identifying those expressions with E_N has been proved here. The gaps
cannot simply be subtracted from the through41 bounds, M2, or a scalar
recurrence floor. Square maximization at other source heights and a
uniform useful gain through later physical kernels remain unresolved.

### An exact six-label cluster retains all joint choices

For N>=12, the actual source admits a stronger exact calculation on
D={1,3,7,9,21,63}. This includes all36 ordered terms of its six-label
square. It does not compute the square maximum for all divisors of Q_N.

The complete mod63 marginal follows from the same literal originals.
In each mod9 row j, the following seven roots have full mass n_j/(7u);
one further root has reduced mass n_j*(u-5/7)/u. Every other entry is zero.

| mod9 row j | Full seven roots | Reduced seven root |
| --- | --- | --- |
| 0 |0,3,4,5|2|
| 3 |3,4,5|0|
| 1,4,7 |0,2,3,4,5|1|

Pure7 removes root6 and width (1-u)-1/7 inside root1. On old root0,
P1 removes root1 and the deeper P cylinders remove that width inside
root2. On old cell3, Q1 also removes root2 and deeper Q removes that
width inside root0. The seven mask is identical at every raw35 point
in a row, proving this actual joint marginal. The existing source
partition checks all63 masses directly at its verification heights.
For mu_r, multiply each entire row by its declared cell weight.

For either measure m put

    E_D(m)=sum_(d,e in D)c_m(lcm(d,e))
          =c_m(1)+3c_m(3)+3c_m(7)+5c_m(9)+9c_m(21)+15c_m(63),
    M_D(m)=max_layout integral L_D^2 dm.                (PG5)

The exact search keeps all3*7*9*21=3969 choices at labels3,7,9,21.
For their load L0=1+I3+I7+I9+I21, the best final63 residue adds exactly
max_y m(y)[2L0(y)+1]. Thus all250047 layouts are covered, including
incompatible residues and residues outside individual maximizing sets.
The producer clears one common rational denominator, compares integer
objectives, retains every maximizing layout and directly checks its
pointwise square. No common-center restriction is imposed on the search.

A finite box certificate extends this optimization to every N>=12.
Allow independent parameters

    t in[t12,1/18], q in[q12,1/4], u in[5/6,u12],
    t12=(1-3^-10)/18, q12=(1-5^-12)/4, u12=(5+7^-12)/6.

After multiplying masses by u>0, full entries are n_j/7 and reduced
entries n_j*(u-5/7). Each entry, and hence each fixed layout's scaled
square, is separately affine in t,q,u. Its difference from any fixed
competitor is the convex interpolation of the eight corner differences.
At all eight corners, exhaustive search for both laws gives exactly
three centered maximizers: mod9 cell4 with seven root3,4,5 for mu, and
mod9 cell3 with seven root3,4,5 for mu_r. The same three layouts therefore
maximize throughout the box. In particular centers4 and3 are respective
fixed witnesses. This is a computed conclusion about this cluster.

The corner checks also establish the fixed cap choices, except that
the plain21 cap can change old root inside the containing box. Its exact
formula is max(n0+n3,R)/(7u), where R=n1+n4+n7. Directly evaluating PG5
at a maximizing layout yields, with A0r=(11/8)(1-a)n0+(5/4)(1-2a)n3,

    E_D(mu)-M_D(mu)=[9(max(n0+n3,R)-R)+15(n3-n4)]/(7u),
    E_D(mu_r)-M_D(mu_r)=3(R-A0r).                       (PG6)

These are valid for every N>=12. On the actual family, write
h=3^(2-N),v=5^-N. Then n0+n3-R=[h(1+v)-6v]/36>0, since
h/v=9(5/3)^N>6. The maximum in the first formula can be removed there.

| Law | M_D divided by source mass, N=12 | Exact normalized gap, N=12 |
| --- | --- | --- |
| mu/S |664143379826325168668383/106896619363526394066296|35632431348732953309967/106896619363526394066296|
| mu_r/T |1591571349732425795009615/240369043020445468666057|27167753242115761212321/240369043020445468666057|

The two gaps are0.333335437181... and0.113025175375... . Their limits
are1/3 and183/1619, while the normalized maxima tend to671/108 and
10720/1619. The local layout set is fixed and finite, so its maximum is
continuous in the marginal masses; the limiting values follow either
from PG6 or the exact limiting marginal calculation.

All remaining full-layout terms retain their original entrywise bounds.
Thus PG6 replaces the overlapping five-term correction in PG3/PG4;
it is not added to it. The limiting plain correction grows by a factor30.
For the currently used reweighting, the additional limiting correction
is only29/4857. This remains a same-source cluster improvement, not a
uniform guard bound or a subtraction from the different WF/A2 estimates.

## The actual near-J source can attain the unit refund exactly

For the actual F12 source above, a true square-maximizing complete layout
and five actual later APs attain the old-marginal unit refund with positive
charge. This brings [15's clean-cylinder mechanism](../001-064/15-a-clean-cylinder-makes-all-current-prime-pair-caps-exact.md)
and [01's uniform 315 unit-refund obstruction](../001-064/01-survivor-reduction.md#uniform-sharp-head-obstruction-to-an-excess-energy-rebate)
into the present near-J guard. The argument uses one jointly realizable
layout throughout; its true maximum is not replaced by an entrywise cap
sum. It is an ordinary deduction from the existing mechanisms.

Retain the literal F_N residues above, N>=3, and put Q_N=105^N. Let R_N
be the set avoiding all its original classes, including mixed 7, and H_N
normalized Haar measure on this period. Thus

    dmu=1_(R_N) dH_N/u, S=mu(1), nu=mu/S.                (UR1)

Every complete layout has one independent residue for each divisor of
Q_N, including its unit once. Its maximum Gamma_Q_N(nu) is attained,
because the layout space is finite. At N=12 the source has 204 original
classes, delta=1-qJ=0.00003388634450980418...<1/4000 and
rho=0.0642857815054542...>3/50, as verified above.

### Two clean coordinates preserve a true maximum

The entire roots x5=4 mod5 and x7=4,5 mod7 avoid every original involving
their respective coordinate. Also x5=20 mod25 avoids every original
involving 5: at depth 1 the possible residues are 1,2,3; at depth 2 they
are 5,10,15; at larger depths they are divisible by 25. There is no original
involving both 5 and 7. Consequently the exact survivor mask factors as

    1_(R_N)(x3,x5,x7)=A3(x3) A35(x3,x5) A37(x3,x7),

where all original exclusions remain in these zero-one factors.

Start with any complete layout. Replace the 7-component of every test
with positive 7-exponent e by 4 mod 7^e, keeping its other components fixed.
For an ordered pair whose maximum 7-exponent is k>0, its original
7-intersection is empty or one depth-k cylinder. At each fixed (x3,x5),
its Haar integral against A37 is at most 7^-k. The replacement gives the
nested clean cylinder 4 mod 7^k and attains 7^-k. The other-coordinate test
conditions are unchanged, so this ordered-pair integral cannot decrease.
Pairs with both 7-exponents zero are unchanged. Summing proves that the
complete square does not decrease. Next replace every positive 5-component
by 4 mod 5^b; the same argument applies using A35. Both replacements are
global legal residue choices, made once for each original test label.

Applying these operations to an attained maximizer gives a maximizer L*
whose positive 5 and positive 7 tests all follow their nested 4 paths:

    integral (L*)^2 dnu=Gamma_Q_N(nu).                   (UR2)

The N pure 3 original cylinders are pairwise disjoint, with one at each of the
depths 1,...,N. Their survivor set A_N in Z/3^N Z has (3^N+1)/2 points.
The N nonunit pure 3 tests of L* cover at most
sum_(h=1..N)3^(N-h)=(3^N-1)/2 points. Hence some a in A_N misses all
those tests; at N=12 the exact comparison is 265721>265720. On

    C_a={x3=a mod3^N, x5=20 mod25, x7=5 mod7},

the source survives completely, while every nonunit test of L* is false:
positive 5 and positive 7 tests miss their respective coordinate, and the
remaining tests are the pure 3 ones just excluded. Therefore L*=1 on C_a.
For general N, existence follows from finite maximization and this count.
At N=12, (FS1) below identifies the complete centered4 layout as a maximum.

### Five actual next 11 labels charge precisely that cylinder

Adjoin the pure class 10 mod 11. For i,j in {0,1}, adjoin one class with
numerical modulus 11*3^N*25^i*7^j and CRT conditions

    x3=a mod3^N, x11=i+2j mod11,
    x5=20 mod25 if i=1, x7=5 mod7 if j=1.               (UR3)

These five odd numerical moduli are distinct and new, and every old
exponent remains within Q_N. The extended family has N^2+5N+5 classes,
hence 209 at N=12. Every old private integer lifts to a private integer
by choosing its 11-digit 9. Each new mixed class has the private CRT point
(a,20,5,i+2j): its old coordinates survive, and its 11-digit distinguishes
it from the other four new classes. The pure 11 class is private at
(4,4,4,10). The point (4,4,4,9) still survives all classes. Thus this is
an irredundant actual extension and a noncover, with period 11*Q_N.

Use the full-Haar 11 base and the existing head parameter delta11=3/10.
At an old source point x, the number of active mixed classes is

    m(x)=1_(x3=a)(1+1_(x5=20 mod25))(1+1_(x7=5 mod7)).

Their 11-digits are distinct and differ from the pure forbidden digit 10,
so the actual forbidden fraction is alpha(x)=(1+m(x))/11. For the
normalized BBMST clipped kernel K11, the actual forbidden row mass is
b(x)=(alpha(x)-3/10)_+/(7/10). Its complete table is

| m |0|1|2|4|
| --- | ---: | ---: | ---: | ---: |
| alpha |1/11|2/11|3/11|5/11|
| b |0|0|0|17/77|

Exactly m=4 occurs on C_a. Put P=nu K11, let B11 be this actual new
forbidden union, and let kappa=P restricted to B11. Since nu is already
supported on all old survivors, kappa is the actual first-hit charge.
For the projection pi to old coordinates its pushforward is

    eta=pi_*kappa=(17/77)1_(C_a)nu <= nu,
    ell_N=eta(1)=17/(77*175*3^N*u*S), 0<ell_N<=17/77<1.                 (UR4)

Here nu(C_a)=1/(175*3^N*u*S), since C_a is entirely surviving. Also
pi_*P=nu, so integrating any old load against eta is precisely integrating
its pullback against kappa. No already removed mixed 7 mass is charged.

Extend Gamma homogeneously to finite positive measures. Every complete
old L>=1 gives integral L^2 d(nu-eta)<=Gamma_Q_N(nu)-ell_N.
The same L* from UR2 attains equality because L*=1 on C_a. Thus

    Gamma_Q_N(nu-eta)=Gamma_Q_N(nu)-ell_N,
    Gamma_Q_N((nu-eta)/(1-ell_N))
      =(Gamma_Q_N(nu)-ell_N)/(1-ell_N).                 (UR5)

Equivalently, the minimum over complete L of
Gamma_Q_N(nu)-integral L^2 dnu+integral(L^2-1)deta is zero.
At N=12 the exact positive charge is

    ell_12=46895305009765625/3527588438996371004187768
          =1.3293870818759043...*10^-8.                 (UR6)

### Old 3 reweighting and the scope of the obstruction

The proof applies separately to every strictly positive r on Z/3^N Z:
set T=integral r dmu and nu_r=r*mu/T, with 0<T<infinity. In each compression
comparison r(x3) is a fixed nonnegative multiplier. Choose a maximizer
for this law and then its uncovered a. The same extension gives

    eta_r=(17/77)1_(C_a)nu_r,
    ell_r=17*r(a)/(77*175*3^N*u*T)>0,                  (UR7)

and UR5 holds with nu_r,eta_r,ell_r. This includes the stated cell weights
r=(11/8,5/4,1,1,1). The maximizing layout and a may change with r;
no single choice is claimed to work simultaneously for all weights.

For the unweighted sequence, 3^N*ell_N tends to 68/9625 and
ell_N/(1-qJ) tends to 34/86625. The charge therefore tends to zero while
qJ tends to 1 and rho tends to 9/140>3/50. This rules out an extra rebate
required to be strictly positive for every positive actual charge in
this guard. This depth-N construction alone leaves open bounds with a
macroscopic charge requirement or an explicit loss allowance. UR5 concerns only the old-marginal square;
it does not assert saturation of a complete 11 transfer. No value of true
Gamma, Lean result, or unrestricted odd-covering
conclusion is supplied.

### The same extension has a complete next11 bound

Root9 is entirely clean. Its actual root mass c for m=0,1,2,4 is respectively
1/10,1/9,1/8,10/77. By the same clean-root comparison, the full killed square
maximum on period11*Q_N is the maximum, over independent old layouts A0,A1, of

    integral[(1-b)A0^2+c(2A0*A1+A1^2)]dnu.

Put J=Gamma_Q_N(nu), E={x3=a mod3^N}, and

    Jp_N=1+sum_(j=1..N)(2j+1)/p^j,
    W_N=(N+1)^2*J5_N*J7_N/(3^N*u*S).

The actual domination nu<=Haar/(u*S), followed by expansion of every original
pair on E, gives integral_E A^2 dnu<=W_N: its three-coordinate pair has at
most(N+1)^2 choices, and each five/seven intersection costs at most its
corresponding p^-max depth. Now 0<=c-1/10<=(23/770)1_E and
2A0*A1+A1^2<=A0^2+2A1^2. Cauchy--Schwarz gives the upper bound below;
A0=A1=L* and L*=1 on C_a give the lower bound:

    (13/10)J-ell_N <= Gamma_(11Q_N)(nu K11^-)
                   <= (13/10)J-ell_N+(69/770)W_N.        (UR8)

Divide by1-ell_N for the normalized killed law. For nu_r replace W_N by
max(r)(N+1)^2*J5_N*J7_N/(3^N*u*T), using its own L*,a,ell_r. Since
J5_N<=15/8 and J7_N<=14/9, the error is O(N^2*3^-N) for the plain law
and the stated fixed cell weights. This controls exactly this five-label
extension, with every old test retained, rather than arbitrary future
inventories. Its coefficient approaches13/10; unit-refund sharpness does
not supply the coarser full-cap coefficient107/77.

### A separate fixed-depth extension retains a positive charge floor

For the plain source law and, separately, the fixed weights
r=(11/8,5/4,1,1,1), a further compression gives a hole of depth at most4.
This stronger version uses the literal F_N restrictions; it does not
apply to an arbitrary positive function r(x3). Assume N>=4.

After the two clean-coordinate compressions, map every three-prefix
of every test by the following common rule, keeping its exponent:

| Depth | Original positive-source prefix | Image |
| --- | --- | --- |
|1|root0 or1|the same root|
|2|row0 or3 modulo9|the same row|
|2|row1,4 or7 modulo9|row4|
|at least3|root1|4 modulo its original power of3|
|at least3|root0, row3|3 modulo its original power of3|
|at least3|root0, row0|18 modulo its original power of3|

Prefixes lying in a pure3 forbidden class may be mapped to any of the
allowed images of their depth: every original pair involving such a
prefix has zero source integral. For any compatible pair with positive
source integral, the displayed images remain compatible. At each fixed
(x5,x7), its old three-intersection is one cylinder at the larger depth.
For depth at least3 the image has the same Haar width and avoids every
pure3 original. In root1, row4 retains precisely the common 3*5 exclusions;
row1 has additional 9*5 exclusions and row7 has additional higher3*5
exclusions. The seven masks are identical throughout root1. On rows0 and3,
the five/seven masks are constant; the path18 also removes any deeper
pure3 exclusion from row0. Thus the image permits every fixed (x5,x7)
permitted throughout the original cylinder, and possibly more. At depth2
the same row domination applies, and depth1 is unchanged. The two stated
weightings are constant on every moved positive-source row. Integrating
proves that every ordered-pair term cannot decrease. An originally
incompatible or zero-mass pair cannot decrease either.

Applying this legal simultaneous map to a true maximizer therefore
retains a true maximizer L*. All its pure3 tests of depth at least3 now
follow one of the three paths3,4,18. Consider

    E1={x3=1 mod9},   E2={x3=12 mod27},
    E3={x3=54 mod81}, (h_i,a_i)=(2,1),(3,12),(4,54).

All three cylinders avoid every pure3 original and every canonical test
of depth at least3. There is one pure3 test at each of depths1 and2.
If the depth1 test chooses root0, it misses E1, and the depth2 image,
which is0,3 or4, also misses E1. If it chooses root1, it misses E2 and E3;
their distinct mod9 rows3 and0 prevent the single depth2 test from meeting
both. Hence some E_i is missed by every nonunit pure3 test. On

    C_i=E_i intersect{x5=20 mod25,x7=5 mod7},

the actual source survives and L*=1. Use UR3 with(h_i,a_i) in place of
(N,a), leaving every old exponent and original class unchanged. This
selects one of three explicit five-label inventories. The same actual
private-point and kernel arguments give

    eta_i=(17/77)1_(C_i)nu,
    ell_i=17/(77*175*3^h_i*u*S),
    Gamma_Q_N(nu-eta_i)=Gamma_Q_N(nu)-ell_i.             (UR9)

Since h_i<=4 and u*S=H_N(R_N)<=1,

    ell_i>=17/(77*175*81)=17/1091475>0.

The source-specific lower bound17/(77*175*81*u*S) tends to
68/779625>0. For the fixed weighted law replace S by T and multiply the
numerator by r(a_i mod9). These three weights are1,5/4,11/8; since
min_i r(a_i)/3^h_i=11/(8*81) and u*T<=11/8, the same uniform floor
17/1091475 holds. The chosen i and maximizer can differ between the two
laws, and no limiting selected i is asserted.

These are guarded sources for every N>=12. Indeed delta_N decreases
with N and delta12<1/4000. Put v=7^-N, M=(1-q)(1/3-t) and
c(v)=(1-v)/5-6/[7(5+v)]. The exact formulas give
rho=T2+c(v)M, T2=(1-q)/90+(1-t)/20+1/360. On this range
T2>=7/120, M>=5/24, c(v)>=c(7^-12)>0, hence

    rho>=51316401261402157493/798255130763894466005>3/50.

Thus a positive extra old-square rebate cannot hold for every extension
even with a charge requirement ell>=c0 for any0<c0<=17/1091475. A larger
charge requirement or an explicit error allowance remains unaddressed.
This is separate from UR3--UR8's depth-N inventory: substituting h_i forN
in the fibre width of UR8 removes its vanishing-error conclusion.

The quantifier is: for each of the two fixed source laws there exists a
later inventory attaining UR9. For UR7 the broader quantifier is: for
each positive old3 reweighting there exists its own depth-N inventory.
Neither gives a single later inventory working for every weighting.
These results do not exclude choosing the head law after seeing the
complete future family, or jointly optimizing all new blocks.

The existing producer checks the three clean cylinders, all six shallow
test choices, actual private integers for all three inventories, the
kernel table and exact charge floors at its applicable verification
heights. These finite checks support the ordinary compression proof;
they do not compute Gamma or its selected maximizing hole.

## The direct square allocation cannot continue through the scalar recurrence

This is a numerical consumption of the existing source/operator and killed-unit interfaces, not a new generic transfer theorem. It concerns the same fixed(3,4)full-Haar head as339. All original powers and independent own-test residues remain.

Let phi(v)=v^2-1. In339(IR10)--(IR12), replace h_t by phi. The zero7 centered comparison is(6/5)phi, so the modified cell costs are kappa_l phi, kappa_l=6/5-zeta_l. For these costs42(A2) has q_(n,l)=n f_l, bar f_l=f_l/4, complete ternary-depth increment kappa_l(b_l+1)/9, and positive5 coefficients7/8 and5/8. Hence its exact modified zero7 contribution is

    P=max_b[sum_l eta_l*kappa_l*(b_l^2-1)+max_l kappa_l*(b_l+1)/9],
    F=max_b[sum_l kappa_l*(n_l+eta_l/4)*(b_l^2-1)
                +max_l kappa_l*(d_l+1/4)*(b_l+1)/9]
           +(7/8)sum_l eta_l*kappa_l+(5/8)P.

All sums converge as polynomial times geometric tails. Retain the unchanged explicit positive7 complement. On each of the nine containing source vertices the resulting centered-square cost is304687/57624, versus the old263/48. The same positive WF transport gives

    integral(L^2-1)dmu <= M2=1220880809/230496000.

The two head square factors are51/35 and67/48, with product J2=1139/560. Let z be the actual unnormalized through13 survivor mass and E(S)=eS-D as339. Before head killing the full square integral is at most J2(M2+S). Every complete test is at least1 on the actual head-deleted set of mass S-z. Subtract that unit square before the sole normalization, giving the allocated upper

    Gamma13<=1+[J2*M2+(J2-1)S]/z
            <=g(S):=1+[J2*M2+(J2-1)S]/(eS-D).

This is decreasing in S on E(S)>0. From339(IR2),(IR8) and s<=1/4+delta0/2,

    S<=1/4+delta0/2-a(1/8-delta0/12)-b(1/12-delta0/9)
      =123557689/576240000=:Smax,
    g(S)>=g(Smax)=334490138381673633/3923164203788188>85.

The lower bound here is on the allocated upper-bound formula g, NOT on actual Gamma13. Replacing g by a smaller valid bound would be a different method.

Combine the [unit refund in327](327-actual-two-prime-survival-needs-a-masked-moment.md)
with the [arbitrary-head transfer](../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md).
Without an additional masked deficit, this scalar procedure assigns

    R_p(F,d)=F[d(1+a_p-d)-b_p]/[d(1-d)-b_p F],
    a_p=(3p-1)/(p-1)^2, b_p=1/[4(p-1)^2], 0<d<1,

with strictly positive denominator. To derive it, start from a normalized
old-survivor law with Gamma<=F. The full kernel gives
`G=(1+a_p/(1-d))*F`; its actual deleted mass ell is at most
`q=b_p*F/[d(1-d)]`. Every complete test has unit at least1, so conditioning
on actual survivors gives at most `(G-ell)/(1-ell)`. Since G>=1, this
ratio increases with ell, and replacing ell by q in both places gives
R_p when q<1. The same actual deleted mass is thus used in numerator and
denominator before its bound is inserted. For fixed d this is increasing in F on its legal domain: writing v=d(1-d),u=v+a_p d-b_p, the difference at F2>=F1 is

    u*v*(F2-F1)/[(v-b_pF2)(v-b_pF1)]>=0.

Here u>0 because v>b_pF2>=b_p. If F2 is legal then every1<=F1<=F2 is legal, so the comparison also holds when thresholds are selected adaptively from previous scalar bounds.

For any proposed input f and output lower k>f, the inequality R_p(f,d)>k follows on every legal d if

    (k-f)d^2+(f-k+a_p f)d+b_p f(k-1)>0.

Three exact all-real quadratic certificates are:

| p | f | k | 4AC-B^2 |
|---|---:|---:|---:|
|17|85|171|625111/16384|
|19|171|480|8981/324|
|23|480|1000|4544192000/14641|

Each leading coefficient A=k-f and each displayed slack is positive, proving positivity without a numerical threshold grid. Thus every choice of legal later clipping parameters from this allocated seed has scalar bound above1000 after23, if it has not already lost its positive denominator. At29, legality requires F<(29-1)^2=784 since d(1-d)<=1/4. It therefore cannot continue.

This rejects the direct weighted square allocation followed by this scalar majorant, even with its unit refund and arbitrary later thresholds. It says nothing negative about actual surviving mass, improved nonlinear or masked estimates, another initial law, another head, or the unrestricted odd-covering problem. In particular it does not invalidate339's positive through37 hinge certificate, which carries a richer state.

The [sharpness and scalar-boundary producer](../../frontier/source-budgets/source_mean_sharpness.py)
replays the quadratic source operator, its unchanged complement, the
complete head multiplier and all three completed-square identities.
Their exact data share the [same canonical certificate](../../certificates/source_norms/source-budgets/source_mean_sharpness.json)
as the limiting-mean theorem above. The common report and one producer
retain the mathematical results and exact checks without a separate
search transcript.

## A fixed reweighted actual source survives through41

Under the same effective9, original noncontainment and original numerical
modulus7 hypotheses of(IR8), the stronger source guard

    qJ>=1-1/4000, rho>=3/50                              (RW1)

implies positive actual survival through41. Use cell weights
`r=(11/8,5/4,1,1,1)` in the ordered surviving mod9 cells(0,3,1,4,7),
with the same chart orientation as(IR8). Keep the full-Haar11/13
thresholds(3,4), then use thresholds(6,8,9,12,16,20,23) at
primes(17,19,23,29,31,37,41). Relative to the reweighted supported13
probability, the complete actual survivor mass through41 is greater
than1/125. In particular, a finite original family satisfying(RW1)
whose prime factors are all at most41 cannot cover the integers.
All original exponent heights and own-test residues are retained.

The rho condition3/50 is stronger than(IR7)'s7/125. The new F12 above
satisfies(RW1), establishing a nonempty source domain. It is a noncover.
No optimal weights, through43 or all-prime continuation is claimed.

### One new law, the same actual forbidden sets

Define the finite positive measure and its total mass by

    dmu_r=r(x mod9)dmu, T=mu_r(1).

Its normalized initial probability is mu_r/T. The full-Haar clipped
kernel at a prefix x uses only the actual forbidden fibre, its current
Haar fraction alpha_x and the fixed threshold. Changing the old point
weights does not change these kernels or their caps. On the common
raw physical chain, the new measure equals r times the old measure.
Since1<=r<=11/8, both have exactly the same actual survivor support.
The weights persist on the original3 coordinate at every later stage.

Normalize the new actual head survivors once, using their own mass z_r.
Positive survival under this probability proves an actual surviving
integer; its numerical masses are relative to this new supported13 law.

### A finite-delta lower bound for the weighted mass

Let mu0,muB be the post-seven masses in cells0 and3, and muR the sum
in the three root1 cells. Then S=mu0+muB+muR and exactly

    T=(11/8)S-(1/8)muB-(3/8)muR.                       (RW2)

The containing-chart inequalities of329 give
`z<=3/4+delta/4`, `alpha1>=(1-delta)/4`,
`betaR>=(1-delta)/4`, `lateR>=(1-delta)/72`.
Writing d_l=z-alpha_ROOT(l)-beta_l>=0, discard only the nonnegative
pure-deficit terms in the original raw35 formula to obtain

    nR<=sum_R d_l/9-lateR<=1/8+5delta/24,
    nB<=z/9<=1/12+delta/36.

Thus(IR8) gives the actual post-seven capacities

    muB<=CB(delta)=(1-zeta_B)(1/12+delta/36),
    muR<=CR(delta)=1/8+5delta/24.

Combining(RW2) with(WF4), with no assumption of attaining these
capacities simultaneously, proves

    T>=L_r(rho,delta)
      :=(11/8)[3/20+rho-(263/360)delta]-CB(delta)/8-3CR(delta)/8.
                                                               (RW3)

The coefficient ofdelta is-26257337/24202080<0. Hence the fixed error
budget delta0=1/4000 gives a uniform lower bound for everydelta<=delta0.
At rho=3/50 it is

    T>=22726567063/96808320000=0.234758407779414... .     (RW4)

This bounds the same actual weighted measure, without asserting a
realizable capacity optimizer. qJ,rho and S0 retain329's definitions.

### Every original source cost carries its cell weight

Keep p_n from(IR11), and for rational t>=1 and e>=0 define

    Q_(t,e)(v)=sum_(n>e)(p_n/n)[h_t(nv)-h_t(n)],
    s_r^Lambda=sum_l r_l*n_l.

The complete cell-dependent source bound is

    B_t^r(theta)=s_r^Lambda*E h_t(N7)
       +F_theta(r_l[Q_(t,0)-zeta_l*h_t])
       +sum_(e>=1)F_theta(r_l*Q_(t,e)).                 (RW5)

Here F_theta is exactly42(A2), with the original d,n,eta. This follows
by multiplying the same-original decomposition(IR10) by r_l before
comparison. The zero7 saving acts on its own original block; every
positive7 block and the constant term also receive r_l. The multiplier
is independent of the current5/7 coordinate and fixed before choosing
any original test, so the pointwise centered Jensen arguments apply.

All transformed costs are nonnegative, increasing, convex and vanish
at1. Multiplication by positive r_l preserves these facts and the
nonnegative deep increments in42(A3)--(A5). WF3 therefore still gives
`integral h_t(L)dmu_r <=lambda B_t^r(theta*)`, with the same
lambda=1+7delta0. The nine containing vertices control every fixed
nonnegative combination of these costs by separate convexity; the
maximum is taken after forming each complete payment.

All tails in(RW5) are complete. For an eventual affine cost av+b with
entrance k, the remaining7-block coefficient is
`a[E(N7;N7>=k)-(k-1)Pr(N7>=k)]` times F_theta(r_l*(v-1)).
The cell-dependent5 tails likewise retain both probability and first
moment, with slopes multiplied by r_l. No original exponent cutoff is
imposed. A sufficient same-measure mean bound is

    integral(L-1)dmu_r<=M_r:=lambda max_theta B_1^r(theta)
       =129284945411/193616640000.                     (RW6)

### The complete head and the unit refund use massT

Reuse(IR17)'s complete11 count atoms and tails, but replace every
source hinge by B_t^r and the source mean by M_r. Explicitly,

    C13^r(theta)=lambda sum_(n<4)u_n*n*B_(4/n)^r(theta)+T1*M_r,
    D_r=max_theta[lambda B_3^r(theta)/7+C13^r(theta)/8]
       =8070958205846453/90196311744000000,
    z_r>=E_r(T):=e*T-D_r, e=74535/74536.                (RW7)

At(RW4), the denominator is
`26206200489324719/180392623488000000>0`. Thus the sole normalization
on actual head survivors is legitimate for every source in(RW1).
Pure11/13 powers are included in the actual bad unions and paid by the
unit labels, as before.

For a later target p,t retain(IR19)'s full count product W, post13-only
product Z, their low atoms and complete tails. Put

    C_p^r=lambda max_theta sum_(n<t)u_n*n*B_(t/n)^r(theta)+T1*M_r,
    c_p'=T1-t*T0, f_p=E(Z-t)_+.

The complete physical integral is at most C_p^r+c_p'*T. Each original
through13 block still includes its unit, so the post13 comparison
functional is pointwise at least f_p on the mass removed at the head.
Subtracting f_p*(T-z_r) before normalizing gives

    H_(<p,t)<=f_p+[C_p^r+(c_p'-f_p)T]/(e*T-D_r).        (RW8)

Here c_p'>=f_p>=0. The floor uses Z only, and is not multiplied by a
maximum cell weight. All quantities refer to the same reweighted law.
Later assigned charges are evaluated under their full incoming physical
laws; domination of earlier killed sets gives the same union bound.

Define Fq,Kq as in(IR21), Cq^r=sum k_p*C_p^r, and

    Aq=(1-Fq)e-Kq, Bq^r=(1-Fq)D_r+Cq^r.

Then the actual normalized surviving mass obeys

    eta_(<=q)^r(1)>=(Aq*T-Bq^r)/(e*T-D_r).              (RW9)

The exact coefficients have Aq>0 and
`e*Bq^r-Aq*D_r=e*Cq^r+Kq*D_r>0` at each of the seven rows.
Consequently(RW3) can be substituted in the increasing lower bound.
At rho=3/50 and q=41, exact rational arithmetic gives

    eta_(<=41)^r(1)>=0.008224657647256354...>1/125.      (RW10)

The strict source threshold from the same fixed formula is
rho>0.05912956428530256...; (RW1) is a simpler sufficient condition.
At rho=9/140 the lower bound is0.0468207220070943...>1/25.
All displayed comparisons use exact fractions.

The new actual F12 has204 distinct original labels with private integers,
delta=0.00003388634450980418... and rho=0.0642857815054542... . Its
post-seven cell masses are the earlier exact w_l*n_l, so directly

    T=sum_l r_l*w_l*n_l
     =240369043020445468666057/997697958915599121093750.

It satisfies(RW1)--(RW4). This family has the residues of the sharpness
construction, including pure49 residue8; it is distinct from the earlier
N12 benchmark. Its private witnesses establish original noncontainment.

The existing[source consumer](../../frontier/source-budgets/source_own_test_consumer.py)
and[canonical certificate](../../certificates/source_norms/source-budgets/source_own_test_consumer.json)
retain `reweighted_full_haar_chain`: all new hinges and complete tails,
the mass bound, exact guard and actual F12. The generalized operator
reproduces every inherited hinge at r=1 and reuses the finite construction
code without consuming its dependent certificate. Replay the existing
`source_own_test_consumer.py --check` command. These are ordinary proofs
and exact arithmetic, not new Lean declarations.

### Fixed cell weights cannot close the present square/scalar route

There is also a uniform limitation for **every** fixed nonnegative
five-cell weight r, including unequal root1 weights. It concerns the
current WF/A2 assigned square numerator, the fixed(3,4)head and the
unit-refund scalar recurrence above; it is not a lower bound on actual
Gamma and does not invalidate the complete-hinge survival result(RW10).

Put phi(v)=v^2-1. The square form of42(A2), already used above, is

    P_k=max_b[sum eta_l*k_l*(b_l^2-1)+max_l k_l*(b_l+1)/9],
    F(k phi)=max_b[sum k_l*(n_l+eta_l/4)*(b_l^2-1)
                 +max_l k_l*(d_l+1/4)*(b_l+1)/9]
             +(7/8)sum eta_l*k_l+(5/8)P_k.

For each cell, the average of b_l^2-1 over the ten baselines is23/10.
Replace both maxima by these averages and discard nonnegative deep terms.
Since n_l<=3eta_l/4 on the containing face, every k_l>=0 satisfies

    F(k phi)>=sum k_l[(23/10)n_l+(231/80)eta_l]
             >=(123/20)sum k_l*n_l.                   (RW11)

The seven comparison square has E N7=6/5 and E N7^2=5/3. Thus its
assigned centered numerator at each containing vertex is

    B_r=(2/3)sum r_l*n_l+(7/15)F(r phi)+F((6/5-zeta)r phi)
       >=(131/12)sum r_l*w_l*n_l
                    +(143/30)sum r_l*zeta_l*n_l.

Let W_r=sum r_l*w_l*n_l. Pointwise domination gives
`max B_r >=(131/12)max W_r`; no common maximizing vertex is required.
IR8 and WF3 give T<=lambda max W_r, while the prescribed assigned
square upper is M2_r=lambda max B_r. Therefore M2_r/T>=131/12 whenever
T>0. ZeroT cannot define a normalized law. With J2=1139/560 and the
nonnegative head payment D_r, any positive head denominator gives

    g_r=1+[J2*M2_r+(J2-1)T]/(eT-D_r)
       >=1+[J2*(131/12)+J2-1]/e=216789167/8944200>24.   (RW12)

For the scalar recurrence already defined above, use the exact positive
quadratic Q from its three-row obstruction. The certificate now supplies
25 fixed(p,f,k) rows, covering every prime17 through127. They start
(17,24,34), end(127,12354,58341), and satisfy A=k-f>0 and4AC-B^2>0.
The producer verifies every intervening prime, linked input/output floor,
and exact completed-square identity. No numerical minimization enters
this finite certificate. Monotonicity in the input makes each row valid
for every legal threshold, including adaptive choices.

At131 a positive scalar denominator requires F<(131-1)^2=16900,
but the carried floor exceeds58341. The prescribed route therefore fails
by131 for every such r and clipping schedule, or earlier if a denominator
fails. A better source numerator, different head, or richer joint state
is outside this obstruction. It identifies a limitation of changing only
these cell weights within that allocated square/scalar procedure.

## Both complete F12 squares have an exact centered maximizer

For the actual204-class F12 constructed above, let Q=105^12 and let
nu=mu/S be its normalized surviving law. Each complete layout has one
arbitrary residue at every divisor d of Q, including the unit. Then

    Gamma_Q(nu)=max_layout integral L^2 dnu
      =2036574313467845778288943/80172464522644795549722
      =25.402416223497948... .                         (FS1)

A maximizing layout puts every test at the residue of4 modulo its own
modulus. This optimizes all2197 labels and their complete square on the
actual source. The fixed weighted law has the same maximizing layout,
with its separate exact value in(FS7). The period and original inventory
are both fixed at N=12. These results do not establish another height,
a statement about every source, or an unrestricted covering conclusion.

### Actual cylinder masses and the common compression

Apply the simultaneous clean5/7 compression in(UR2), followed by the
common three-prefix map above. A maximum is retained, and every positive
five or seven test follows its nested4 path. The remaining three choices
are0/1 at depth1,0/3/4 at depth2, and18/3/4 at depths at least3.
These transformations are performed once per original test label, so all
pair intersections still belong to one legal layout.

Here is the actual mass formula used by the certificate. In the row order
(0,3,1,4,7), put

    eta=(1/9-t,1/9,1/9,1/9,1/9),
    n=((1-q)(1/9-t),(1-q)/9,(1-3q)/9,
       (1-2q)/9,(1-2q)/9-tq),
    sigma=(u-1/7,u-2/7,u,u,u), Z=sum sigma_j*n_j=uS.

Write m(a,r,b,e) for the nu-mass of the test with three residue r at
depth a and clean residues4 at depths b,e. An exponent0 imposes no
condition. For a<=2, let v_j be n_j if b=0 and eta_j if b>0, restricted
to rows congruent to r modulo3^a. For a>=3, only row r modulo9 contributes:
its pure value is3^-a, and its raw35 value is(1-q)3^-a on paths3/18 or
(1-2q)3^-a on path4. Use the raw35 value when b=0 and the pure value
when b>0. Then exactly

    m(a,r,b,e)=[sum_j v_j*(sigma_j if e=0 else1)]
                 /[Z*5^b*7^e].                       (FS2)

The clean positive7 cylinders avoid every original seven restriction;
positive5 cylinders avoid every original five restriction. This proves
the two cases in(FS2), with all original exclusions through depth12
retained. The normalized pair mass is zero for incompatible three
prefixes. Otherwise it is(FS2) at the coordinatewise maximum exponents
and the deeper three prefix. These are actual intersections, not their
separate cap maxima.

The retained[exact source API](../../frontier/source-budgets/source_full_square.py)
implements these masses. The[flow verifier](../../frontier/source-budgets/verify_source_full_square.py)
independently partitions each coordinate by the literal original APs and
all queried tests before comparing the6084 canonical cylinder masses.
It checks the three-prefix intersection rule and both nested-coordinate
rules against those partition masks. The complete centered layout is
integrated a second time from these original-membership counts.

### A two-choice upper comparison preserves the common root assignment

The169 labels with a=0 are fixed. At each of the2028 remaining labels i,
call the unique root1 choice g_i good, and the one or two root0 choices
bad. Good/bad intersections are zero because their three residues differ
modulo3. For a choice r at i, let u_i(r) be its diagonal mass plus twice
the sum of its intersections with every fixed label. For i<j define

    a_i=max_(r bad at i)u_i(r)-u_i(g_i),
    G_ij=2*m(i,g_i;j,g_j),
    B_ij=2*max_(r bad at i,s bad at j)m(i,r;j,s).

All G_ij and B_ij are nonnegative. For an actual layout, put s_i=1
exactly when label i uses a bad choice. Its square gain above the all-good
centered layout is at most

    F(s)=sum_i a_i*s_i
      +sum_(i<j)[-G_ij*(s_i+s_j)+(G_ij+B_ij)*s_i*s_j]. (FS3)

Both good gives pair gain0, a mixed pair gives-G_ij, and both bad gives
at most B_ij-G_ij. Each s_i is shared by every occurrence of its label.
Only the remaining choices within the bad root are maximized separately;
this is an upper comparison and asserts no simultaneous attainment of
those maxima.

Set b_ij=G_ij+B_ij and d_i=2a_i+sum_(j!=i)(B_ij-G_ij). For binary s,

    2F(s)=sum_i d_i*s_i-sum_(i<j)b_ij*abs(s_i-s_j).     (FS4)

Choose a positive integer D making every D*d_i and D*b_ij integral.
Join source to i with capacity D*d_i when d_i>0, join i to sink with
capacity-D*d_i when d_i<0, and put one edge of capacity D*b_ij in each
direction between i and j. Let R=sum_(d_i>0)D*d_i. The cut whose source
side contains exactly the indices with s_i=1 has capacity

    R-2D*F(s).                                        (FS5)

Any nonnegative capacity-feasible flow conserved at every other vertex,
with source-to-sink value v, implies F(s)<=(R-v)/(2D) for every layout.
Thus a feasible flow with v=R proves all gains nonpositive. The actual
all-good layout attains gain0, closing the maximum. No claim that a flow
search algorithm found a maximum is needed.

### Exact complete certificate and its scope

The retained[sparse integer flow](../../certificates/source_norms/source-budgets/source_full_square_flow.json)
has

    D=160344929045289591099444,
    R=v=209626201609934585576758.

The verifier reconstructs all2055378 unordered free-label pairs and all
4111200 positive directed capacities. It checks all31364 saved nonzero
flows against their actual capacities and conservation at all2030
vertices. Omitted flow entries are zero; duplicate, unknown and malformed
entries are rejected. It checks that v equals the full sum of positive
source capacities. Some cylinder masses require scale2D internally; each
final graph capacity is checked to divide exactly back to scaleD.

For the centered layout, the number of ordered exponent pairs with
maximum a is2a+1. Consequently its complete square is exactly

    sum_(a,b,e=0..12)(2a+1)(2b+1)(2e+1)
                         *m(a,4 modulo3^a,b,e),       (FS6)

which gives(FS1). There is no omitted-label or omitted-pair tail in this
certificate. The existing `source_mean_sharpness.py --check` replay now
includes this source and flow verification and records its exact result
in the existing sharpness certificate. The flow checker can also be run
directly with `python3 -I -S -O` and uses only the standard library.
This is an ordinary mathematical proof with exact finite verification;
no new Lean declaration or frozen theorem is asserted.

### Three pure9 test branches close the fixed weighted law

For the same actual F12 and the fixed row weights
r=(11/8,5/4,1,1,1), let nu_r=r*mu/T. Its complete maximum is

    Gamma_Q(nu_r)
      =16622960794401007994531582/721107129061336405998171
      =23.051998967253425... .                         (FS7)

The complete centered4 layout again attains this value. The source API
uses(FS2) with each row multiplied by r_j and Z replaced by uT. Its
normalization and all6084 cylinders are checked against the same literal
original APs, with the declared row weights. Both the source inventory
and all2197 test labels, including the unit once, remain complete.

After the proved simultaneous compression, the pure9 test has exactly
three possible residues0,3,4. Fix this one test in turn to c=0,3,4.
This divides layouts into three exhaustive branches; it does not
condition the source probability law on a residue event. Every integral
in all three branches uses the identical nu_r. Let a=(2,0,0) be this
test label, and write I_c for its indicator at residue c.

The169 labels of three-exponent0 and the fixed pure9 test now form the
170 fixed labels. The other2027 labels retain their good/bad root choices.
Their branch unary is exactly

    u_i^c(r)=u_i(r)+2*m(i,r;a,c).                      (FS8)

Thus the anchor's intersections are retained. For the branch reference
layout put L_c=L_4+I_c-I_4, where L_4 is the complete centered load, and
let C_r=integral L_4^2 dnu_r. Its exact baseline shift is

    Delta_c=integral[2L_4*(I_c-I_4)+(I_c-I_4)^2]dnu_r. (FS9)

The verifier sums the first term over all original test labels and the
second as m(I_c)+m(I_4)-2m(I_c intersect I_4). This retains the fixed test's
diagonal and every interaction, including its interactions with the
other fixed labels.

Use the graph of(FS3)--(FS5) on the remaining free labels, with unaries
(FS8). If its source capacity is R_c and a feasible flow has value v_c,
every actual layout in branch c has square at most

    U_c=C_r+Delta_c+(R_c-v_c)/(2D).                   (FS10)

The fixed test changes unaries and the reference constant, while mixed
good/bad free pairs still have zero mass. This remains an upper bound
when the residual choices within the bad root are optimized separately
for each pair. Neither their joint attainability nor equality of U_c
with the branch optimum is required.

The exact certificates for
[c=0](../../certificates/source_norms/source-budgets/source_full_square_r0_flow.json),
[c=3](../../certificates/source_norms/source-budgets/source_full_square_r3_flow.json), and
[c=4](../../certificates/source_norms/source-budgets/source_full_square_r4_flow.json)
all use D=1442214258122672811996342. They give

| Fixed pure9 test residue c | Exact U_c-C_r | U_c, decimal approximation |
| --- | --- | --- |
|0|-1360086135549916732057219/1442214258122672811996342|22.10894482124856|
|3|-134181193906862145805493/480738086040890937332114|22.77288400257087|
|4|0|23.051998967253425|

In branch4, Delta_4=0 and the feasible flow saturates every source edge:

    R_4=v_4=4250337641076669357482784.                 (FS11)

The other two branch upper bounds are strictly below C_r. Every canonical
layout therefore has square at most C_r, and the legal complete centered4
layout attains C_r. The simultaneous compression proves(FS7) over all
original layouts. This does not claim uniqueness of a maximizing layout
or a restriction on the pure9 residue before compression.

For each branch the verifier reconstructs all2053351 free-label pair
blocks and4108729 positive directed capacities. It checks391109,238026,
and461363 nonzero flow entries, respectively, and conservation at all2029
vertices. All source integrals, baseline shifts and graph calculations
are exact. The weighted witnesses use the existing lossless compressed
certificate format; its reader restores and verifies every original flow
triple before the same independent capacity checks run. The source law
is never replaced by a relaxed marginal or a separately normalized row.

The existing sharpness producer now verifies all four flow certificates
and records both exact maxima. A standalone complete replay is

    python3 -I -S -O docs/reports/erdos7-odd-covering/frontier/source-budgets/verify_source_full_square.py --all

These two source values remove an optimization gap for the specified
finite family. They do not supply a uniform maximum over all admissible
sources or prove that the later-prime survival inequalities close.
