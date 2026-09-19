[Index](../marked_head_profile.md) · [Actual source parameters](42-whole-hinge-absorption-sharpens-actual-survival.md) · [Constant-barrier boundary](44-constant-survival-barriers-leave-a-structural-gap.md)

# Actual source compatibility separates two relaxed mass endpoints

The actual source labels impose an additional mass constraint beyond
the five-cell density and cylinder-cap relaxation. Every forbidden modulus has at most
one original residue. All constructions below use exactly one residue
at every nonunit modulus in a finite357 exponent box; they are not
asserted to cover the integers.

1. Both source parameter vectors theta398 and theta402 are limits of
   actual finite original-label families.
2. The joint point(theta398,S=53/360) is also approachable, so its
   existing mass cap D398 is sharp in this closure.
3. Every sequence of actual families with theta tending to theta402
   satisfies liminf S>=139/900=3/20+1/225. Thus(theta402,D402) is
   excluded from the closure.
4. An explicit sequence has(theta,S)->(theta402,7/45). Consequently
   the infimum of limiting S-values at theta402 is between139/900
   and140/900. The sharper two-depth inequality and matching
   construction in [profile50](50-sharp-source-survival-endpoints.md)
   determine the exact infimum as233/1500; the bounds here remain valid.

The exclusion in item3 holds for arbitrary residues of every mixed7
label and every finite exponent height. It uses source exclusions
that remain visible to two old-coordinate carrier caps, without any
assumption about the intersection pattern of mixed7 classes. These
are ordinary proofs; no Lean verification is claimed. Independent
finite constructions are checked by the program linked below.

Both limiting source parameters have

    deficit=(1/2,0,0,0,0), alpha=(0,1/4),
    beta=(0,0,1/4,0,0), z=3/4,
    eta=(1/18,1/9,1/9,1/9,1/9),
    d=(3/4,3/4,1/4,1/2,1/2), s=1/4.

They differ in the location of the complete late budget:

| Source vector | late | n | Existing D |
| --- | --- | --- | --- |
| theta398 | (1/72,0,0,0,0) | (1/36,1/12,1/36,1/18,1/18) | 53/360 |
| theta402 | (0,0,1/72,0,0) | (1/24,1/12,1/72,1/18,1/18) | 3/20 |

The labels398 and402 refer to the canonical source-vertex enumeration.
They do not count original moduli. In particular, neither source
vector can be removed from the actual parameter closure; the new
exclusion concerns its joint pairing with S=D.

## 1. Actual measures and complete budgets

Use raw ternary Haar restricted to the actual pure3 survivor, eta,
and the raw actual35 survivor measure Lambda. Its ternary marginal
is lambda. In the effective9 branch the five surviving mod9 cells
have roots ROOT=(0,0,1,1,1). Put

    eta_l=(1-deficit_l)/9, sum deficit_l<=1/2,
    d_l=z-alpha_ROOT(l)-beta_l,
    n_l=eta_l*d_l-late_l, s=sum_l n_l.

Here z is the actual pure5 survivor mass; alpha and beta are the
actual additional five-coordinate deletion measures of the3*5^b
and9*5^b source classes in their respective roots/cells. In particular,

    z>=3/4, sum alpha<=1/4, sum beta<=1/4,
    late_l>=0, sum late_l<=1/72.

The late measure is the additional deletion by the original labels
3^a5^b with a>=3,b>=1, after pure3, pure5 and the shallow mixed35
classes have already been removed. Its complete raw budget is

    sum_(a>=3,b>=1)3^-a*5^-b=(1/18)*(1/4)=1/72.     (SC1)

Let nu7 be the normalized actual pure7 survivor measure, whose
unnormalized mass u7 is at least5/6. For any seven-adic cylinder
E_e of depth e,

    nu7(E_e)<=7^-e/u7<=6/(5*7^e)=u_e,
    sum_(e>=1)u_e=1/5.                             (SC2)

Before mixed7 deletion the measure is Lambda tensor nu7. If V is
the complement of the actual mixed7 forbidden union, the surviving
mass in this normalization is

    S=(Lambda tensor nu7)(V).

This is the same S=s*M(V) in the source profiles. It is not the
unnormalized three-coordinate Haar survivor mass, which is u7*S.

Write h=sum eta_l, h0=eta0+eta1 and h1=eta2+eta3+eta4. The pure3
budget alone implies

    h>=1/2, h0<=2/9, h1>=5/18,
    eta2>=1/18, h1-h0>=1/18.                       (SC3)

In particular h1 is the larger pure3 root mass for this branch.
The complete old-coordinate cap sum underlying D is

    C=R(n)+max(n)+max(d)/18
                    +(h+h1+max(eta))/4+1/72,
    D=s-C/5.                                      (SC4)

The positive5 part comes from complete5 sums at old3 depths0,1,2,
followed by the remaining old3 tail. Its individual cofactor5 term
is h/5, and its individual cofactor15 term is h1/5.

## 2. A strict source neighbourhood forces four different5 slots

Suppose

    z<79/100, alpha1>21/100, beta2>21/100.          (SC5)

The original source modulus5 must be present. If absent, its full
remaining pure5 removal budget is only sum_(b>=2)5^-b=1/20, which
would give z>=19/20. Let P5 be that modulus5 cylinder. The original
modulus25 must also be present, with its first-level parent P25
different from P5. Omitting25, or nesting it in P5, loses at least
1/25 from the complete pure5 removal budget1/4 and gives z>=79/100.

The original modulus15 must lie on ternary root1: otherwise the
entire alpha1 contribution is bounded by the b>=2 tail1/20. Let
P15 be its first-level five-coordinate cylinder. If P15=P5, the
first label contributes nothing after pure5 deletion. If P15=P25,
the source25 class removes at least1/25 of its five-coordinate
mass, so

    alpha1<=1/5-1/25+sum_(b>=2)5^-b=21/100.

Both alternatives contradict(SC5). Therefore P15 differs from
P5 and P25.

Similarly, the original modulus45 must lie in cell2. Otherwise
beta2<=1/20. Its first-level five cylinder P45 differs from P5
and P15, which are already entirely deleted in cell2. It also
differs from P25: coincidence loses the pure25 mass1/25 and gives
beta2<=21/100. Thus P5,P25,P15,P45 are four distinct first-level
five-adic cylinders. Let X be the fifth.

These deductions concern the actual source labels5,25,15,45. They
impose no equality on the residues of any later mixed7 label.

## 3. Near-full late deletion puts a definite mass in the fifth slot

Let

    epsilon=1/72-late2>=0,
    c_(a,b)=3^-a*5^-b, a>=3,b>=1.

Partition the actual additional late deletion in cell2 among the
finite original deep mixed35 labels, assigning each removed point
to the first class containing it in an arbitrary fixed ordering.
Let q_(a,b) be the assigned raw measure; put q=0 for absent labels.
Then

    0<=q_(a,b)<=c_(a,b),
    sum_(a,b)q_(a,b)=late2,
    sum_(a,b)(c_(a,b)-q_(a,b))=epsilon.             (SC6)

The last equality includes all absent labels and their complete
infinite cap tails. Every summand is nonnegative.

Call a b=1 label good if its ternary cylinder lies in cell2 and
its five-coordinate cylinder is X. An absent label is not good.
Every other b=1 label obeys

    q_(a,1)<=4*c_(a,1)/5.                          (SC7)

Indeed it either lies outside cell2, is absent, or uses one of the
four other5 slots. In P5,P15,P45 it is already removed in cell2
by a shallow source class. In P25, the source25 cylinder removes
exactly one fifth of its full raw five cylinder. Pure3 or other
source exclusions can only decrease its actual contribution.

Since sum_(a>=3)c_(a,1)=1/90, write the mass assigned to good labels as

    sum_good q_(a,1)
      =1/90-sum_not-good c_(a,1)
                     -sum_good(c_(a,1)-q_(a,1))
      >=1/90-5*epsilon.

The inequality uses c<=5(c-q) for the non-good labels from(SC7),
and then bounds all the remaining nonnegative losses by(SC6).
The actual late deletion in cell2 over X is therefore at least

    g=(1/90-5*epsilon)_+, 0<=g<=1/90.              (SC8)

The assignment prevents any double-counting of overlapping deep
source classes. No disjointness of the original deep labels was
assumed in this universal argument.

## 4. Two complete mixed7 carrier families each lose this mass

Let m5 be the largest Lambda mass of any old-coordinate cofactor5
cylinder, and m15 the largest Lambda mass of any old-coordinate
cofactor15 cylinder:

    m5=max_P Lambda(Z3 x P),
    m15=max_(r,P) Lambda([r]_3 x P).

For m5, the guaranteed losses relative to h/5 in the five slots
P5,P25,P15,P45,X are respectively

    h/5, h/25, h1/5, eta2/5, g.

By(SC3), every one of the first four is at least1/90, hence at
least g. These are separate lower bounds in separate slots; no
addition of potentially overlapping losses is needed. Thus

    m5<=h/5-g.                                    (SC9)

For cofactor15 on root1, the corresponding losses relative to h1/5
are h1/5,h1/25,h1/5,eta2/5,g. Again all are at least g. Root0 is
bounded directly by

    h0/5<=h1/5-1/90<=h1/5-g;

the third root has no pure3 survivors. Consequently

    m15<=h1/5-g.                                  (SC10)

The maxima in(SC9)--(SC10) range over every residue available to
each mixed7 label. For example the later modulus15*7^e is free to
choose a different ternary/five residue from the source modulus15.

Replace just these two individual cofactor caps in(SC4) by their
improved values. All other caps stay unchanged. The resulting old
cap sum is at most C-2g. Its individual summands are nonnegative,
so the complete physical7 caps(SC2) apply with their original
direction. For arbitrary choices of every mixed7 residue, the
union bound gives

    S>=s-(C-2g)/5=D+2g/5.

Using(SC8), this is exactly

    S>=D+(2*late2-7/300)_+                         (SC11)

under(SC5). This proof neither assumes nor requires a positive
overlap between mixed7 masks. Missing labels only decrease the
actual union and are still covered by the complete cap sums.

If also late2>=1/72-1/900, the correction in(SC11) is at least
1/450. At theta402 it tends to1/225. Since D is continuous in
the displayed source parameters, any sequence tending to theta402
eventually satisfies(SC5) and obeys

    liminf S>=3/20+1/225=139/900.                   (SC12)

## 5. A continuous inequality valid on the whole actual domain

Define the nonnegative source cap slacks

    epsilon_z=z-3/4,
    epsilon_alpha=1/4-alpha1,
    epsilon_beta=1/4-beta2,
    E=epsilon_z+epsilon_alpha+epsilon_beta,
    L=2*late2-7/300-E/9.

Then every actual family in the effective9 branch satisfies

    S>=D+[L]_+.                                   (SC13)

On(SC5), E>=0 gives [L]_+<=(2*late2-7/300)_+, so(SC11) proves it.
Outside(SC5), at least one of the three cap slacks is at least1/25.
Because late2<=1/72,

    L<=1/225-(1/25)/9=0.

There(SC13) is the existing S>=D. These two cases cover equality
on all three boundary planes as well.

The lower bound in(SC13) is continuous, and has the same1/225 gain
at theta402. It is max(D,D+L), so separate concavity of D and D+L
does not imply separate concavity of their maximum. The original
1296 product-vertex interpolation cannot be applied to this new
maximum without an additional partition or another valid extension
argument. Equation(SC13) is an actual-family inequality, not a
claim about every point of the former relaxed parameter box.

## 6. Finite source families approaching both parameter vectors

Use the surviving mod9 cells

    C0=[0]_9, C1=[3]_9, C2=[1]_9, C3=[4]_9, C4=[7]_9.

The source pure3 classes of moduli3 and9 are[2]_3 and[6]_9. For
a>=3, c in{0,3,1,4,7}, and j=1,2, define

    T_a(c,j)=[c+j*3^(a-1)]_(3^a).

For fixed c the T_a(c,j) are pairwise disjoint in(a,j): above the
two fixed ternary digits of c, their first nonzero digit occurs
at position a-1 and has value j. Each fixed-j family has total
mass sum_(a>=3)3^-a=1/18.

For j=1,2,3,4 and b>=1 define

    F_(j,b)=[j*5^(b-1)]_(5^b).

All these cylinders are pairwise disjoint in(j,b), by their first
nonzero five-adic digit. Each fixed-j family has complete mass1/4.

For a finite N>=3 use only exponents at most N. The source classes
common to both constructions are

    modulus3^a, a>=3:       T_a(0,1),
    modulus5^b:            F_(1,b),
    modulus3*5^b:          [1]_3 x F_(2,b),
    modulus9*5^b:          C2 x F_(3,b).

For the original deep mixed35 labels3^a5^b, a>=3,b>=1, choose

    construction398:       T_a(0,2) x F_(2,b),
    construction402:       T_a(1,1) x F_(4,b).       (SC14)

Each rectangle determines its unique original residue by CRT.
In construction398, these late rectangles lie in C0, avoid the
pure3 cylinders T_a(0,1), and avoid the root1 shallow exclusions.
Their F2 coordinates avoid pure5 F1. In construction402 they lie
in C2, avoid the pure3 deletions in C0, and their F4 coordinates
avoid F1,F2,F3. All late rectangles contribute their full raw
product masses and are pairwise disjoint.

The exact finite complete sums are

    t_N=sum_(a=3..N)3^-a=(1-3^(2-N))/18,
    q_N=sum_(b=1..N)5^-b=(1-5^-N)/4.               (SC15)

Thus both constructions have

    deficit=(9*t_N,0,0,0,0),
    alpha=(0,q_N), beta=(0,0,q_N,0,0), z=1-q_N,

while late is(t_N*q_N,0,0,0,0) for398 and
(0,0,t_N*q_N,0,0) for402. In either construction

    s_N=5/9-t_N-q_N.                               (SC16)

Indeed sum eta_l*d_l=5/9-t_N-q_N+t_N*q_N, and the late deletion
subtracts exactly t_N*q_N. Taking N to infinity gives the two
specified theta vectors, including all five n_l and d_l values.
This establishes attainability of the source parameters themselves.

## 7. Five disjoint mixed7 classes attain the stated endpoints

For j=1,...,6 and e>=1 define

    G_(j,e)=[j*7^(e-1)]_(7^e).

These are pairwise disjoint in(j,e). Use G_(6,e) for source pure7
modulus7^e. For every other cofactor3^a5^b use the following old
carrier and seven digit class j:

| Class j | Original cofactor | Old-coordinate carrier |
|---|---|---|
|1|3|[1]_3 x Z5|
|1|9|C1 x Z5|
|2|3^a, a>=3|T_a(3,1) x Z5|
|3|5^b, b>=1|Z3 x F_(4,b)|
|4|3*5^b, b>=1|[1]_3 x F_(4,b)|
|5|9*5^b, b>=1|C1 x F_(4,b)|
|5|3^a5^b, a>=3,b>=1|T_a(4,1) x F_(4,b)|

For the original modulus3^a5^b7^e, choose this old carrier and
G_(j,e). The construction deliberately shares a seven cylinder
within each class; this is a chosen witness, not a restriction on
arbitrary families in the preceding theorem.

Within class1 the two ternary carriers lie on different roots.
Class2 has disjoint ternary cylinders. Classes3 and4 have disjoint
five cylinders. Within class5 the a=2 cylinders lie in C1, while
the a>=3 cylinders lie in C3; within the latter subgroup, different
a or b give disjoint rectangles. Thus each class has disjoint old
carriers. Distinct classes or distinct e have disjoint seven
cylinders. All mixed7 rectangles are consequently pairwise disjoint
before source restriction and avoid every pure7 forbidden class.

Take0<=a,b,e<=N and omit only(a,b,e)=(0,0,0). Together with the
source classes, this is exactly one residue at each of
(N+1)^3-1 distinct odd nonunit original moduli. It imposes no
requirement that residues at different moduli agree.

The pure7 survivor mass and normalized mass of one seven digit
class are exactly

    u7_N=1-sum_(e=1..N)7^-e=(5+7^-N)/6,
    kappa_N=sum_(e=1..N)7^-e/u7_N
           =(1-7^-N)/(5+7^-N).                    (SC17)

Let delta=0 for398 and delta=1 for402, and write t=t_N,q=q_N.
The sums of raw Lambda masses of the five old-carrier classes,
in their order, are

    H1=4/9-(8/9)*q-delta*t*q,
    H2=(1-q)*t,
    H3=(5/9-(1+delta)*t)*q,
    H4=(1/3-delta*t)*q,
    H5=(1/9+t)*q.                                 (SC18)

For H1, the surviving root1 mass is1/3-7q/9-delta*t*q and C1 has
mass(1-q)/9. For H2 the cylinders lie in unaffected C1 and retain
five fraction1-q. On F4, construction398 has all pure3 survivors,
of mass5/9-t, while402 loses the additional ternary late set of
mass t; this proves H3. Restricting the same F4 calculation to
root1 gives H4. The C1 and C3 carriers of H5 have no late deletion
in either construction. These arguments establish each term of
(SC18) directly on the actual finite source measure.

Their total is

    H_N=4/9+t+q/9-(1+3*delta)*t*q.                 (SC19)

By the disjointness already proved, the exact surviving mass is

    S_N=s_N-kappa_N*H_N.                           (SC20)

All three exponent tails are displayed explicitly in(SC15) and
(SC17); no cutoff is substituted for a complete infinite bound.

For398, H_N tends to37/72. Since s_N tends to1/4 and kappa_N to1/5,

    S_N ->1/4-(1/5)*(37/72)=53/360=D398.            (SC21)

For402, H_N tends to17/36, so

    S_N ->1/4-(1/5)*(17/36)=7/45.                  (SC22)

The extra mass above D402 is1/180. In this witness, the complete
5^b and3*5^b cofactor families each lose1/72 of their old-coordinate
cap sums because their F4 carriers meet the late deletion in C2.
Multiplication by the complete7 factor1/5 gives
(1/5)*(1/72+1/72)=1/180. This is a source-carrier loss; the mixed7
union itself is disjoint in the witness.

Combining(SC12) and(SC22) yields the stated interval for the402
limiting infimum. The construction(SC21) rules out any universal
strict mass gain at(theta398,D398). Neither statement resolves
the unrestricted covering problem or its later-prime continuation.

## Exact constructive verification and scope

[source_mass_compatibility.py](../frontier/source_mass_compatibility.py)
builds both original-label families at heights3,4,5. It checks every
five-cell mass and each of the five old-carrier totals, unique original
moduli, disjoint old carriers within each class, disjoint seven cylinders,
and the exact normalization in(SC17). The families contain63,124,215
original moduli respectively. At height3 it independently takes the union
of all CRT residue classes in the full period105^3=1157625 and checks
the exact surviving mass. These computations agree with(SC15)--(SC20).
They also satisfy both applicable source-compatibility inequalities.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source_mass_compatibility.py
```

The command exits zero and is read-only; `--output PATH` writes the
exact finite results. The finite checks verify the explicit examples.
The ordinary argument above supplies the quantification over all
original families and the infinite limiting statements.

No new global K bound follows merely by excluding one endpoint.
The continuous positive-part constraint needs a valid partition or
other interpolation argument before entering the fixed-target consumer.
Profile50 determines the exact402 infimum as233/1500. The unrestricted
covering problem remains open.
