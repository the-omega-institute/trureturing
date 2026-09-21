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

The remaining sections continue in `339b-the-actual-near-j-source-and-the-unit-refund.md`.
