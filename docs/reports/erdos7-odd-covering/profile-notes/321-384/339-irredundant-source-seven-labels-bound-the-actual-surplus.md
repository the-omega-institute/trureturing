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
