# Integrated root profiles, conditional intersections and finite-core criteria

Actual conditional support profiles give a sufficient complete-query
certificate even when some root fibres have no survivor. Combining this
certificate with the pointwise collision estimate preserves every success
of [report563's collision criterion](563-prefix-free-rooted-labels-admit-all-later-four-mixed-towers.md)
on P={3,5,7,11,13,17,19}.
An irredundant thirteen-label family passes the new certificate and fails
that report's fixed collision criterion. This is a strict extension of a
sufficient certificate, not a claim that this finite family was previously
unknown to be noncovering.

A uniform theorem follows when the rooted mixed originals at each of the
first five root exponents share one root residue, independent of their
remaining numerical part. The five residues need not lie on one root path
or have disjoint cylinders. All higher root phases, all other exponents
and phases, and every old mixed tower on L={11,13,17,19} remain arbitrary.
Section6 proves a common query bound11.011636<565/51 and positive Haar
survival after arbitrary23/29-touching additions.

Actual arithmetic counterexamples identify the remaining obstruction:
a twelve-label irredundant family has an empty positive-mass root fibre,
and a two-label family shows that applying the support polynomial to
averaged loads can overstate the actual survivor mass. Section7 gives an
irredundant110032-label family for which even the integrated IP3 certificate
falls below its query threshold, despite saturated actual root-cylinder caps.
Section8 retains one proper-support intersection and certifies every finite
height in this counterexample family. Its height-five core also permits
arbitrary additional P-smooth originals outside the finite exponent box,
including previously omitted non-rooted supports, with query bound11.051678.
Keeping the full channel intersections reduces the required core to height
three and12549 labels, with query bound9.933538 after the entire outside-box
charge. The low-box originals and their phases remain prescribed.
Neither arbitrary root overlap nor unrestricted Erdős #7 is resolved. The results use ordinary
proofs and exact rational computation; no Lean verification is claimed.

## 1. Keep the actual conditional profile before integrating

Let P={3,5,7,11,13,17,19}, Q=P minus{3}. Fix any finite family of distinct
nonunit P-smooth numerical moduli and their original residues. Every
finite height and every mixed support is allowed in this section.
Let S_p be the actual pure-p survivor and use the single product source

    nu0=nu3 x nuQ, nu_p=H_p(.|S_p), nuQ=product_(q in Q)nu_q.

For each x3 in S3 and nonempty S subset Q, let E_S(x3) be the union of
the Q-events of all actual mixed originals whose Q-support is S and whose
3-part, if present, matches x3. Originals with no3 factor are always active.
Set p_S(x3)=nuQ(E_S(x3)). These are exact unions under the same Q-source,
including all same-support phases and overlaps between numerical labels.
Only this fixed family's avoidance calculation uses the union; numerical
identities are retained for collision charges and continuation tasks.

Write

    Phi_R(p)=sum_(F pairwise-disjoint nonempty supports inside R)
                  (-1)^|F| product_(S in F)p_S,
    h(x3)=Phi_Q(p(x3)) if Phi_R(p(x3))>0 for every R subset Q,
          0 otherwise.                                             (IP1)

Then the actual fibre survivor U_x3 satisfies

    nuQ(U_x3)>=h(x3),
    nu0(U)>=G0,  G0=integral h dnu3.                               (IP2)

To prove this, join two scope events when their coordinate supports
intersect. Under the product law nuQ, an event is independent of every
collection of its nonneighbors. On a fibre satisfying IP1, the64 coordinate
tests imply positivity for every induced event subgraph. Indeed

    partial Phi_R/partial p_S=-Phi_(R minus S), S nonempty.

Induction on |R| proves positivity throughout the box from0 to the tested
vector and monotonic decrease in every coordinate. Removing arbitrary
scope events sets their weights to zero, so all induced polynomials are
positive. [Scott--Sokal, Theorem4.1(a)](../../../../../Library/Arith/scottsokal2003repulsive.md)
now gives the first inequality. On an uncertified fibre, zero is a valid
lower bound, even when the fibre actually has survivors. Integration gives
the second inequality. The test is sufficient, not necessary.

Upper bounds on the union probabilities may also be used if all64 tests
are positive for those upper bounds. In particular, sums of the individual
event probabilities give the earlier support-aggregation version. Exact
unions can improve it without replacing the original event family.

All actual root and pure-root cylinders have finite heights. Their finite
laminar partition of S3 makes p and h constant on finitely many regions.
Their masses and the Q-union probabilities are exact finite CRT/source
calculations. This gives a finite certificate for each input family; it
provides no uniform bound on the required computation or certificate size.

## 2. Preserve the collision theorem by taking a pointwise maximum

For this section assume report563's support inventory: every mixed original
either contains3 or is supported on L={11,13,17,19}. Root phases may overlap.
For rooted label3^a*u, let A_(a,u) and B_(a,u) be its actual root and Q
cylinders, and v_(a,u)=nuQ(B_(a,u)). Define

    omega(x3)=sum_u [sum_(a:x3 in A_(a,u))v_(a,u)
                    -max_(a:x3 in A_(a,u))v_(a,u)],
    s0=65869/378675,  Omega=integral omega dnu3,
    g(x3)=max(h(x3), max(0,s0-omega(x3))),
    G=integral g dnu3.                                             (IP3)

The maximum over an empty set is zero. Report563's designation argument
gives nuQ(U_x3)>=max(0,s0-omega(x3)) on each fibre: designate one active
event per numerical u before drawing Q, apply its uniform bound, and
charge the omitted actual events by the union bound under nuQ. Therefore

    nu0(U)>=G>=G0,
    G>=s0-Omega.                                                   (IP4)

The maximum selects between two valid lower bounds on the same fibre and
source; it does not add incompatible savings or select different laws.
Thus all successes of the earlier collision criterion on this P, including its
prefix-free and six-layer corollaries, are retained.

For either IP2 or IP4, write G_* for the chosen positive lower bound.
There is one uniform survivor law rho=H(.|U)=nu0(.|U), and

    R_P(rho)<=5+B5/G_*,
    B5=19132074022251234990036997833948759259
         /18473247078046657922374787501704265625.                   (IP5)

Here R_P sums maximal residue probabilities over all nonunit P-smooth
query labels, including arbitrarily high powers. For each finite query
box choose maximizing phases under this same rho. The pure-product
complete-query comparison in
[report557](557-complete-query-comparison-allows-three-more-old-pair-towers.md)
gives E_nu0(N-5)_+<=B5 uniformly in the box and phases. Conditioning once
on U gives IP5; increasing cofinal boxes give the full nonnegative sum.
No replacement query law is chosen on a root fibre.

In particular G_*>51*B5/310 gives R_P(rho)<565/51 and the existing
positive-survival extension by arbitrary23/29-touching originals with
P-smooth cofactors. No post-extension query bound is asserted. A universal
inequality at this threshold for arbitrary actual profiles is still missing.

## 3. Thirteen irredundant labels separate the two certificates

Take no pure originals, and take

    0 mod15, 36 mod45;
    0 mod product(S), for every pair S subset L;
    1 mod product(S), for every triple S subset L;
    2 mod46189.                                                    (IP6)

There are thirteen distinct odd numerical moduli. The first two have
root cylinders0 mod3 and0 mod9, with the same remaining numerical part5
but different5-residues0 and1. Their full original classes are disjoint;
same-phase redundancy removal cannot eliminate either one.

In fact all thirteen originals are irredundant. CRT witnesses modulo
2078505=9*5*11*13*17*19 are specified as follows:

* For0 mod15, use x3=3 mod9, x5=0, and every late coordinate3.
* For36 mod45, use x3=0 mod9, x5=1, and every late coordinate3.
* For an old support S of size k, use x3=1 mod9, x5=3, the value k-2
  on S, and3 on L minus S.

Each witness belongs to its indicated original and avoids all others.
The result data retain integer representatives and check all memberships.

The old block polynomial is

    Phi_L=1-sum_(pairs S)1/prod(S)-sum_(triples S)1/prod(S)
              +2/46189
         =44801/46189.                                            (IP7)

The positive term accounts for the three disjoint pair-pair selections,
less the single four-coordinate event. All64 coordinate tests on every
root region are positive. The root regions have masses2/3,2/9,1/9;
their5-coordinate forbidden probabilities are0,1/5,2/5. Hence

    G0=G=(41/45)*(44801/46189)=1836841/2078505,
    R_P(rho)<=100759055040065243579847527636422087384
                /16325396203562801717962105960494665625
             =6.171920961898365...<565/51.                         (IP8)

The actual Haar survivor is1841638/2078505. A separate enumeration of
all46189 late-coordinate assignments gives44918 survivors; independent
enumeration of the45 root/5 residues gives41 survivors.

However Omega=1/45, so the old fixed certificate gives

    s0-Omega=57454/378675<51*B5/310,
    5+B5/(s0-Omega)=11.825982611179311...>565/51.                    (IP9)

This separates the sufficient criteria on an actual irredundant family.
It is not a comparison with every existing noncoverage method or every
possible law, and the finite example supplies no universal profile bound.

## 4. A positive-mass root fibre can have no survivor

Take pure originals0 mod3,0 mod5,0 mod7. For each a=1,2,3 take three
rooted originals with CRT coordinates

    x3=1 mod3^a, x5=a;
    x3=1 mod3^a, x7=a;
    x3=1 mod3^a, x5=4, x7=a+3.                                    (IP10)

These twelve moduli are distinct and odd. Their nine mixed
(modulus,residue) pairs, grouped by a, are

    (15,1),   (21,1),   (105,4);
    (45,37),  (63,37),  (315,19);
    (135,28), (189,136),(945,244).

On the root fibre1 mod27 all nine are active. The singleton5 events leave
only x5=4 in its pure survivor; the singleton7 events leave x7=4,5,6.
The three joint5/7 events delete all these possibilities. This fibre
therefore has actual survivor mass zero, although its nu3 mass is1/18.
It refutes a uniformly positive bound on every actual root fibre when
root phases are unrestricted, already within the all-rooted inventory.

The four root strata, indexed by the number j of active depths, have

| j | nu3 mass | Actual Q-fibre survival |
|---|---:|---:|
|0|1/2|1|
|1|1/3|7/12|
|2|1/9|1/4|
|3|1/18|0|

The corresponding scope polynomial on {5,7} is

    (1-j/4)*(1-j/6)-j/24=((4-j)*(6-j)-j)/24.

It equals the displayed actual survival. IP1 uses zero on the last
stratum, and integration gives G0=13/18 exactly. In the full period945,
312 residues survive, giving Haar mass104/315. Every original has a
residue that belongs to it alone, so the obstruction persists on this
irredundant family. The exact witnesses are in the result data.

This does not refute an integrated bound, a differently reweighted
common-law construction, report561, or Erdős #7. It rules out only a
positive lower bound required separately on every root fibre.

## 5. Averaging loads before the polynomial changes the answer

Take0 mod15 and1 mod21, with no pure originals. The root residues0,1,2
give support weights (p5,p7)=(1/5,0),(0,1/7),(0,0), respectively. All
fibres pass the positivity test, and their actual survival is the support
polynomial. Therefore

    integral Phi_Q(p(x3)) dnu3=(4/5+6/7+1)/3=31/35,
    Phi_Q(integral p(x3) dnu3)=(1-1/15)*(1-1/21)=8/9.               (IP11)

The latter overstates actual survival by1/315. Exactly93 of105 residues
survive, independently confirming the first expression. This is an
actual globally fixed arithmetic counterexample to the proposed
mean-field lower bound, not a relaxed nonrealizable support profile.
The root dependence must be retained through the nonlinear calculation.

## 6. Active-depth budgets give a uniform class with overlapping prefixes

Keep the support inventory of Section2. For every positive exponent a,
let A_a^* be the union, inside S3, of the distinct3-local cylinders of all
present rooted mixed originals3^a*u. A root cylinder is counted once in
this union even when many numerical Q-parts use it. Define

    N(x3)=sum_a 1_(A_a^*)(x3),
    beta=E_nu3 N=sum_a nu3(A_a^*),
    p0=nu3(N=0).                                                  (IP12)

The actual finite original family determines these quantities. They count
active depths, not original events, and keep all pure3 exclusions in nu3.

At N=1, only one root exponent is active. Numerical distinctness therefore
gives at most one active rooted label for each complete numerical u.
The support ceilings of report563 apply, so h>=s0. At N=0 only the old
L-events remain. Their full cap polynomial is

    c_old=1-sum_(S subset L, |S|>=2) product_(q in S)1/(q-2)
              +3/(9*11*15*17)
         =2689/2805,
    c_old-2*s0=231277/378675>0.                                   (IP13)

All its induced coordinate polynomials are positive: there are at most
two disjoint old supports, and1 minus the sum of all old weights is
8066/8415>0. The positive-box argument then gives h>=c_old for every
actual old-only profile. At N>=2 use h>=0, whether or not that fibre
passes the stronger profile test. These three cases prove

    h(x3)>=s0*(2-N(x3))+(c_old-2*s0)*1_(N=0)(x3),
    G0>=s0*(2-beta)+(c_old-2*s0)*p0.                              (IP14)

In particular beta<=1 gives G0>=s0 and the same complete-query bound
10.953938953721723 as report563, without requiring disjoint root prefixes.
Dropping the nonnegative p0 term gives the more general sufficient test

    beta<2-51*B5/(310*s0)=1.0204810108393294... .                  (IP15)

This is an actual-source depth-union criterion; arbitrary families are
not asserted to satisfy it. The thirteen- and twelve-label families
above have beta=4/9 and13/18, respectively. Both satisfy the criterion,
and neither requires all root fibres to survive.

### Shared root phases at each depth

Suppose that, for every a, all present rooted labels3^a*u have the same
3-residue alpha_a modulo3^a, independent of u. There is no compatibility
condition between alpha_a at different depths, and all Q-residues may
depend on the full original label. With w3=H3(S3)>=1/2,

    beta<=sum_(a>=1)1/(w3*3^a)=1/(2*w3)<=1.                       (IP16)

Thus IP14 proves the uniform source bound s0 for this whole class, with
arbitrary finite heights and every old-L mixed support. Overlap between
the root cylinders is allowed. The estimate integrates the extra reserve
on zero-depth fibres; it does not require a uniform positive bound on
each multiple-depth fibre, which Section4 disproves.

### Only five shared low depths suffice; every higher phase is arbitrary

It is enough to impose the preceding common-phase condition for a<=D.
For this estimate remove the higher rooted mixed originals temporarily,
while retaining the complete original pure source and all old-L originals.
Let N_low count the active low depths. Since c_old>=2*s0, the same three
cases give the useful affine bound

    low_fibre_survival>=c_old-(c_old-s0)*N_low,
    E_nu3 N_low<=1-3^-D,
    nu0(low_family_survivor)>=s0+(c_old-s0)*3^-D.                  (IP17)

Now charge every higher rooted original under this same nu0. Numerical
distinctness and the complete geometric sums give

    sum_(a>D,u>1) nu0(actual class3^a*u)
       <=[product_(q in Q)(1+1/(q-2))-1]*sum_(a>D)2/3^a
       =(1113/935)*3^-D.                                        (IP18)

The sum is over actual labels, bounded by all possible numerical labels;
all actual residues remain fixed. Every high original is retained among
the constraints defining the final survivor U. Combining IP17 and IP18,
with no change of source, gives

    nu0(U)>=s_D=s0-(153619/378675)*3^-D.                           (IP19)

At D=5 this yields

    s_5=15852548/92018025,
    R_P(H(.|U))<=35044610507390662344298654333344771759
                   /3182507297027885470852331299879202500
                =11.01163555543722...<565/51,
    H(U)>=3963137/100776960.                                     (IP20)

The resulting Haar lower bound after arbitrary distinct23/29-touching
originals with arbitrary P-smooth cofactors and fixed residues is

    637734526107735968960930201833297223
      /2932401053130816752666186337709977600000>0.                 (IP21)

These additions need not satisfy the common-root-phase condition. The
complete query estimate pays them with the same product-extension factor
51/616 used in report563. No complete-query bound after the additional
conditioning is asserted.

For this explicit affine estimate, D=4 gives s_4=5542/32805 and query
bound11.130449711268232, which does not cross the target. The positive
coefficient in IP19 makes five the least integer D for this estimate;
this is not an impossibility claim for four shared depths or for other
source constructions.

IP19 is a bound on the actual full survivor after the charged high
originals. It is not a claim that the full family's IP1 polynomial itself
inherits the low-family polynomial minus that charge. The final uniform
survivor law and the all-height query comparison in IP5 use the actual
mass lower bound, so they remain valid.

## 7. An actual family refutes universal success of the integrated certificate

This is a counterexample to the universal certificate inequality G>51B5/310 on its seven-prime rooted-plus-old-L inventory. It is not an upper bound for actual survivor mass, not a counterexample to noncoverage, and not an impossibility result for other laws or other certificates. The family has an explicit avoiding point. Its110032 originals are distinct numerical moduli; an aggregate private-witness argument also makes it irredundant.

### Fully specified finite arithmetic input

Put P={3,5,7,11,13,17,19}, Q=P minus{3}, L={11,13,17,19}. Set H=8,K=4,A=7. For p prime, digit d different from1, and e>=1, write

    c_p(d,e)=d*p^(e-1)+(p^(e-1)-1)/(p-1),
    C_p(d,e)=[c_p(d,e)] modulo p^e.

Each word consists of e-1 low digits1, then digitd. Cylinders for distinct pairs(d,e) are disjoint. Include every pure original C_p(0,e), p in P,1<=e<=8.

For every nonempty support S subset Q, every exponent tuple(e_q) in{1,2,3,4}^S, and every root exponent1<=a<=7, include one original of numerical modulus

    3^a product_(q in S) q^e_q.

Its Q-coordinates use digits

    d_q(S)=min(|S|+1,q-1),

except that the singleton5 originals at a=2 and singleton7 originals at a>=3 use digit3. Its3-residue is

    r_(a,S)=2 modulo9,                         if S={5},a=2;
             7+9*c_3(2,a-2) modulo3^a,       if S={7},a>=3;
             c_3(2,a) modulo3^a,             otherwise.

The full residue is the CRT residue of these stated local residues, fixed once for every numerical label.

For every S subset L with |S|>=2 and every exponent tuple in{1,2,3,4}^S, include the old original of modulus product q^e_q, with Q-digits |S|+6 on its coordinates. These digits are8,9,10, valid even at11 and disjoint from all relevant rooted channels. There are

    7*8 +7*(5^6-1)+(5^4-1-4*4)=110032

originals. Their support and exponent tuples make numerical moduli distinct. Every mixed original either contains3 or is supported on L. No coordinate, phase, original exponent or pure constraint is omitted.

### The complete actual pure source and exact same-support unions

The actual pure survivor law is nu0=product nu_p, with

    w_p=H_p(S_p)=1-sum_(e=1)^8 p^-e
       =(p-2+p^-8)/(p-1),
    nu_p=H_p(.|S_p),
    t_q=nu_q(union_(e=1)^4 C_q(d,e))
       =(1-q^-4)/(q-2+q^-8), d!=0,1.

Every channel is disjoint from the pure exclusions. Different digit channels are disjoint. For a fixed support S, the union of all its exponent tuples is exactly the Cartesian product of its channels, with mass t_S=product_(q in S)t_q. Distinct channel vectors give disjoint such rectangles. Identical vectors are one actual union event. Therefore all support probabilities below are actual same-support unions, not an uncorrected sum of overlapping events.

In the root coordinate, w3=3281/6561. Let

    A_a=C_3(2,a), a=1,...,7,
    B=[2] modulo9 subset A_1,
    D_a=[7+9*c_3(2,a-2)] modulo3^a subset A_2, a=3,...,7,
    D=union_(a=3)^7 D_a.

The A_a are pairwise disjoint. The D_a are pairwise disjoint, and D is disjoint from B and from all A_a with a>=3. Every one is wholly inside the actual pure3 survivor. In particular EVERY original root cylinder achieves its actual maximum Haar/conditional cap1/(w3*3^a). Pure3 is nearly maximally deleted, and every depth-one original uses the same untouched root. Thus the negative result persists under precisely this strong saturation geometry; the harmful dependence comes from deeper phases.

### Six exact root profiles

Define baseline support weights

    v_S=t_S,                 unless S subset L and |S|>=2;
        2*t_S,               for S subset L and |S|>=2.

Let phi=Phi_Q(v), phi5=Phi_(Q minus{5})(v), phi7=Phi_(Q minus{7})(v), phi57=Phi_L(v). Let c_old be the old-only profile, with weights t_S for old mixed S and zero elsewhere.

There are exactly3281 allowed root residues modulo6561. Their six regions are:

| Root region | Count | Changes from v | Collision omega |
|---|---:|---|---|
| S3 minus union A_a |2|old-only|0|
| A1 minus B |1458|none|0|
| B |729|p5 increases by t5|t5|
| A2 minus D |366|p5 decreases by t5|0|
| D |363|p5 decreases by t5; p7 increases by t7|t7|
| union_(a=3)^7 A_a |363|p7 decreases by t7|0|

Masses are the counts divided by3281. The producer independently reconstructs these counts by enumerating only the6561 root residues and the literal original root phases; it never enumerates the full CRT period.

All64 coordinate-subset polynomials are strictly positive on each profile, verified with exact rational arithmetic. Thus h is the displayed full polynomial everywhere. On B and D, t5 and t7 both exceed s0, so the collision fallback(s0-omega)_+ is zero. On every other region h>=s0. Consequently the IP3 repaired certificate satisfies g=h pointwise, and G=G0.

Multiaffinity makes the first-order changes cancel exactly. The only surviving second-order term is negative on D:

    G=G0=(3279/3281)*phi+(2/3281)*c_old
            -(363/3281)*t5*t7*phi57.

This identity is independently checked against direct averaging of the six full profiles. It pinpoints the obstruction: moving the singleton5 depth-two cylinder removes5-load on A2 and adds it within A1; moving singleton7 deeper cylinders adds7-load inside that same5-depleted A2 region. Both operations preserve every individual depth-cylinder mass and the total marginal support load. Their cross term decreases the integrated nonlinear profile.

The exact result is

    G=11896353657900110917305940184050970099978148851942853
      /69878103243070953218900866574163339591956220339720217
     =0.17024436992112751...,

whereas51B5/310=0.1703834060791555.... Their positive difference is

    4936411433087409357209714770245859112260517126744418900719948116625262002836547044493
    /35504515538274863366028727968178070807877954342958366241989684583167055990970413562656250
    =0.00013903615802800687....

This refutes a universal success claim for the IP3 threshold. Since G is a LOWER bound for actual survival, its failure provides no upper bound on nu0(U). The all-neutral digit word in every coordinate avoids all originals and supplies an explicit actual survivor.

### Irredundancy

There are452 mixed groups, one for each(root depth,support) and each old support. For a target exponent tuple, set each specified Q-coordinate to the full8-digit all-1 word with its one target position changed to the target channel digit; leave unspecified Q-coordinates all1. Other numerical exponent tuples in the same group cannot match, by disjointness of the comb cylinders.

For a rooted target with a=1 choose root5; for a=2 choose root7. Override these by root2 for the modified singleton5,a2 group, and by its literal D_a residue for a modified singleton7,a>=3 group. For all other a>=3 choose c_3(2,a). For an old target use the all-1 root word.

These choices avoid every pure cylinder. A group with a coordinate outside the target support cannot match the neutral coordinate. A proper subset containing a late prime has a different size-dependent channel there; a subset confined to5/7 is separated by its low-support digit, except the modified singleton channels. The root choices5 and7 avoid the latter's B and D locations for any target pair. Equal supports but different ordinary depths are separated by the disjoint A_a; modified equal-support overlaps use different Q-channels. Old groups have distinct higher channels and a neutral root.

The program checks all452 aggregate private witnesses against every mixed group. Channel membership is independent of the target exponent position, so this lifts to every actual exponent tuple. Each pure original has a private witness with its target coordinate's one digit0 and all other coordinates neutral. Irredundancy is stronger than required to refute the certificate inequality.

The [actual-family producer](../../frontier/cover-geometry/actual_profile_threshold_counterexample.py)
and [exact data](../../frontier/cover-geometry/actual_profile_threshold_counterexample.json)
retain the finite input formula, the complete original-label stream digest,
six actual profiles,384 positive coordinate tests and the strict rational
gap. Its1942 checks pass, including the saturated endpoint profiles below. The ordinary channel and private-witness
arguments above explain the realization; the calculation does not prove
an upper bound on actual survival or a Lean theorem.

### Saturated root caps still permit failure

Take the same input formulas with H=A=K=n>=3. Every n specifies a
finite actual family, and every root cylinder still lies wholly inside
the actual pure survivor. As n grows,

    w3->1/2, t_q->1/(q-2), zero_root_mass->0,
    moved_root_mass->1/9.

All64 polynomials of each of the six limiting profiles are positive;
the smallest is8302/378675. The finite profiles lie in their positive
coordinate boxes. On collision regions, t5 and t7 already exceed s0
at n=3 and increase thereafter. On all other regions the polynomial
is at least s0 by the baseline-box comparison. Thus g=h for each n>=3.
At the limiting baseline Phi_Q=s0 and Phi_L=598/935, so the cross-term
identity gives

    G_n -> s0-(1/9)*(1/3)*(1/5)*(598/935)
         =233/1377
         =0.1692084241103849...<51*B5/310.

The limiting target gap is0.0011749819687706168.... Thus even nearly
maximal pure3 deletion and exact saturation of every individual root
cap do not rescue the IP3 threshold. The construction preserves one
shared first-level phase throughout; the loss arises at deeper levels.
The actual-family producer also retains these exact endpoint tests.

### Keeping the actual channel intersections restores the same-law certificate

The same family has substantially more actual survival than its IP3
lower bound. For each q in Q, classify the coordinate by its channel
digit2,...,min(q-1,10), or by the remaining pure-survivor set. Each
listed digit has probability t_q; the remaining atom has probability
1 minus the number of listed digits times t_q. These disjoint atoms
retain all distinctions used by the originals. Their product consists
of240000 Q-atoms, independent of the much larger CRT period.

On each root region, a mixed group forbids exactly the channel
assignments matching its specified digits. Summing the product weights
of assignments avoiding every active group therefore gives the actual
conditional survival, including all cross-support intersections. The
[exact channel calculation](../../frontier/cover-geometry/actual_profile_channel_survival.py)
and [data](../../frontier/cover-geometry/actual_profile_channel_survival.json)
give

    nu0(U)=17173936624779018562508379164956196001660495079666053
             /69878103243070953218900866574163339591956220339720217
          =0.2457699311762869...,
    nu0(U)-G=0.0755255612551594...,
    R_P(H(.|U))<=5+B5/nu0(U)=9.213956670437577...<565/51.

This uses the very same uniform full-survivor law. It shows that this
counterexample is a limitation of the support-probability polynomial,
not of the law or the actual survival threshold. The exact channel
calculation is a consumer for this specified family, not a uniform
bound for arbitrary original phases.

## 8. One conditional containment repairs the profile family

### A scope-preserving residual event

In each actual root fibre, choose nonempty supports T strictly contained
in S. Keep E_T and every other event, and replace only

    E_S by E'_S=E_S minus E_T.

The union of all forbidden events is exactly unchanged. E'_S still
depends only on the coordinates in S, since T is contained in S.
Consequently the same product-source dependency graph and IP1 proof
apply to the residual probabilities p'. No original numerical modulus
or phase is removed from the arithmetic problem.

Write delta=nuQ(E_S intersect E_T). Only p_S changes, by subtracting
delta. The support polynomial is affine in that one coordinate, so

    Phi_Q(p')=Phi_Q(p)+delta*Phi_(Q minus S)(p).                  (IP22)

If the old64 tests are positive, p' lies in their positive box; all
residual tests are positive and the gain in IP22 is nonnegative. If the
old test fails, the residual vector can be tested on its own. Thus the
residual version of h is never smaller than h, and taking its maximum
with the unchanged original collision lower bound never worsens IP3.
This is an ordinary application of the existing avoidance theorem and
PF6 derivative identity. It introduces no new probability law.

For this step, T contained in S is essential to the stated support
assignment. Subtracting an event on unrelated coordinates can enlarge
the support, requiring a different graph. The actual intersection,
not the product of its two marginal probabilities, determines delta.

### One nested event cancels the negative cross term

For the actual family in Section7, take T={7} and S={5,7} in every
root fibre. The pair event uses channel3 at both5 and7. The singleton7
event uses channel2, except that the missing5_extra7 region has both
channels2 and3. It is absent on the missing7 region. Therefore

    E_{5,7} intersect E_7 = E_{5,7} on missing5_extra7,
                           empty on every other region.

The pair has no old non-rooted57 contribution. On the indicated region
its ordinary root-depth2 group is active; the shifted singleton7 group
contains its entire7 projection. These facts concern the full channel
unions over all Q-depth tuples, not one selected residue representative.

Only on this region, replace p_{5,7}=t5*t7 by zero. Its complement
polynomial is Phi_L(v), unchanged by either singleton phase move.
Multiplying IP22 by the actual region mass exactly cancels Section7's
negative cross term. In the H=8,K=4,A=7 example this gives

    G_res=(3279/3281)*Phi_Q(v)+(2/3281)*Phi_old
         =12225336058273944936775148917353902683139470784942853
            /69878103243070953218900866574163339591956220339720217
         =0.17495231683304452...>51*B5/310,
    R_P(H(.|U))<=5+B5/G_res=10.919692060217889....                (IP23)

The actual survivor and the uniform law are those of Section7. This
certificate only needs the one conditional containment, rather than the
full240000-atom calculation of the larger actual survival probability.

### Uniformity at every finite height

Now take H=A=K=n>=3 in the same original construction. Put

    t_q(n)=(1-q^-n)/(q-2+q^-n),
    N_n=(3^n+1)/2,
    d_n=(3^(n-2)-1)/2.

The six root-region counts, out of N_n actual pure-survivor words, are

| Region | Count |
| --- | ---: |
|zero|1|
|base|2*3^(n-2)|
|extra5|3^(n-2)|
|missing5|(3^(n-2)+1)/2|
|missing5_extra7|d_n|
|missing7|d_n|

The moved singleton5 mass equals the total missing5 mass, and the moved
singleton7 mass equals its missing mass. Their linear polynomial terms
therefore cancel in the average. The only mixed term is
-(d_n/N_n)*t5*t7*Phi_L(v), and the residual pair removal cancels it.
Consequently the exact residual polynomial average is

    G_res,n=(1-1/N_n)*Phi_Q(v_n)+(1/N_n)*Phi_old,n.              (IP24)

Here v_n has weights t_S(n), doubled on the old-L mixed supports,
and Phi_old,n uses just those old supports with weight t_S(n).
All t_q(n)<=1/(q-2). Each residual profile lies in the positive box of
its limiting profile; the384 endpoint values are positive, with minimum
8302/378675. The positive-box argument therefore applies for every n.
For the two profiles in IP24 it gives

    Phi_Q(v_n)>=s0=65869/378675,
    Phi_old,n>=c_old=2689/2805,
    nu0(U)>=G_res,n>=s0+(c_old-s0)*2/(3^n+1)>s0.                (IP25)

This proves a uniform complete-query bound, with the all-height
comparison and finite-box exhaustion already supplied by IP5:

    R_P(H(.|U))<=5+B5/s0=10.953938953721723...<565/51.

The query margin is at least0.12449241882729621.... The result covers
arbitrarily large finite n, including the sequence on which the original
IP3 certificate converges to233/1377 below its threshold. It does not
claim a uniform residual-profile bound for arbitrary original phases.

### A fixed height-five core with arbitrary outside originals

Let C_5 be precisely the preceding family with H=A=K=5. It has

    7*5+5*(6^6-1)+(6^4-1-4*5)=234585

distinct original labels. Inside the full exponent box0<=v_p(d)<=5
for every p in P, retain exactly C_5; the other labels of that box are
absent. Outside the box allow ANY finite set of additional distinct
nonunit P-smooth originals, with arbitrary fixed phases. These additions
can be pure or have any mixed support, including supports involving5 or7
without3. No phase or height condition applies outside the box.

Use nu0 from the pure originals of C_5 throughout the argument. For
p in P its mass and saturated cylinder cap are

    w_p=(p-2+p^-5)/(p-1),
    nu_p([r]_(p^e))<=1/(w_p*p^e).

Additional pure originals are charged as new events under this same
source; it is not reconditioned when they are added. The complete sum
of these numerical cylinder caps outside the box is exactly

    J5=product_p(1+1/(p-2+p^-5))
          -product_p((p-1)/(p-2+p^-5))
      =118067598971178844770142374636782853
         /12596688478752606034800835467400970240
      =0.009372907742406166....                                  (IP26)

The two products sum the full and bounded exponent inventories,
including the unit in both. Their difference counts each outside
numerical label once. Numerical distinctness and the union bound thus
pay every permitted new original, without assuming independence.

The exact height-five value in IP24 is

    G_res,5=111026506737532663970505177806321
               /615072679626592091543009544306688.

For the survivor U_full of the complete enlarged family,

    nu0(U_full)>=s5=G_res,5-J5
      =2155755259013490113345803666836671227
         /12596688478752606034800835467400970240
      =0.17113666521559998...>51*B5/310,
    R_P(H(.|U_full))<=5+B5/s5=11.05167711763319...<565/51.       (IP27)

The final law is uniform Haar on U_full because U_full lies in the
retained pure-source product. That source still satisfies all of IP5's
cylinder caps; completeness of its pure inventory was not required
for the conditional convex comparison. Every query height is retained.

Arbitrary additional distinct23/29-touching originals, with arbitrary
P-smooth cofactors and fixed residues, are paid under this one law.
Writing W5=product_p w_p, the remaining Haar mass is at least

    W5*s5*[1-(1+5+B5/s5)*51/616]>0.                            (IP28)

No complete-query bound after this last conditioning is asserted.
The large fixed low-depth core is a genuine hypothesis, not a reduction
of an arbitrary covering family to C_5. Arbitrary low-depth phases and
unrestricted prime support remain unresolved.

### Full intersections reduce the fixed core to three layers

Let C_3 be the same original construction with H=A=K=3. In the full box
0<=v_p(d)<=3 retain exactly C_3, with its prescribed phases and no other
originals. Outside this box permit any finite collection of additional
distinct nonunit P-smooth labels, with arbitrary fixed phases and supports,
including pure labels. This core has only

    7*3+3*(4^6-1)+(4^4-1-4*3)=12549

originals. Its exact channel intersections give the following stronger
consumer of the same outside-box argument.

For clarity the exact finite computation is specified here. The channel
cylinders c_q(d,e) for 1<=e<=n are pairwise disjoint for all digits d!=1:
their base-q words first leave the digit1 at position e. Channel0 is the
pure forbidden union. Under its complement, each channel d>=2 has mass

    t_q(n)=(q^n-1)/((q-2)*q^n+1).

Retain digits D_q={2,...,min(q-1,10)} and one neutral category for their
complement. The latter has mass1-|D_q|*t_q(n). All events use only these
categories. Independent Q-coordinates give exactly240000 channel atoms;
their integer weights are products of q^n-1 for a named digit and
(q-2)*q^n+1-|D_q|*(q^n-1) for a neutral coordinate, with denominator
product_q((q-2)*q^n+1).

An old-L event occurs precisely when at least two late coordinates have
digit8, at least three have digit9, or all four have digit10. On a nonzero
root region a rooted event of size k>=2 occurs precisely when at least k
coordinates q have digit min(k+1,q-1). The remaining rooted singletons
forbid digit2 at each late coordinate. At5 and7 their forbidden digit sets
are, respectively,

| Root region | At5 | At7 |
| --- | --- | --- |
|base|{2}|{2}|
|extra5|{2,3}|{2}|
|missing5|empty|{2}|
|missing5_extra7|empty|{2,3}|
|missing7|{2}|empty|

The zero region has only the old-L events. Thus checking these predicates
on a channel atom decides every original constraint exactly; no product
of marginal event probabilities replaces an intersection. At n=3 the
root counts in the preceding six-region order are1,6,3,2,1,1 out of14.
Summing the allowed atom weights and then these actual root weights gives

    nu0(U_core)=1157864475594883207/3870838428711782528
               =0.2991249820727395....                         (IP29)

Keep this C_3 pure source throughout. Formula IP26 with5 replaced by3
charges every permitted outside original once, giving

    J3=21951298206607522395/246085763698501615616
       =0.08920182084771766...,
    nu0(U_full)>=s3=nu0(U_core)-J3
      =23298254753076498710959/110984679428024228642816
      =0.2099231612250219...>51*B5/310,
    R_P(H(.|U_full))<=5+B5/s3=9.933537751764058...<565/51.       (IP30)

As before, adding pure originals does not reset the source, the final
conditional law is uniform Haar on U_full, and every query height is
covered by IP5. Writing W3=product_p[(p-2+p^-3)/(p-1)], arbitrary additional
distinct originals touching23 or29 with P-smooth cofactors leave Haar mass
at least

    W3*s3*[1-(6+B5/s3)*51/616]
      =0.00472644343391005...>0.                              (IP31)

No query bound after this final conditioning is asserted. The same exact
calculation at n=4 gives a source-mass lower bound after the outside charge
0.23422374465768897 and query bound9.421685949846331. At n=2 the defining
construction still makes sense, with the shifted singleton7 branch empty;
the resulting source-mass lower bound is0.12551894750218565, giving query bound
13.25105580856838, so this certificate fails there. This failure says
nothing about existence of a covering or success of another estimate.
These are specific finite cores; no claim of success for all core heights
or arbitrary low-box layouts is inferred from the three computations.

## 9. Reproduction and remaining uniform obligation

The [producer](../../frontier/cover-geometry/integrated_actual_root_profiles.py)
and [result](../../frontier/cover-geometry/integrated_actual_root_profiles.json)
retain all original labels, irredundancy witnesses, coordinate-subset
polynomials, exact source weights and rational comparisons.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/integrated_actual_root_profiles.py
```

All330 explicit checks pass; `--output` chooses a different result path.
The finite computations certify the stated examples and constants. The
source argument, all-induced positivity implication and complete-query
comparison supply the ordinary proof of the conditional general criterion.
The active-depth inequalities and geometric tail charge prove the uniform
classes in Section6; the program also checks their exact constants and
their application to the two earlier actual families.

The [proper-support consumer](../../frontier/cover-geometry/proper_support_profile_residual.py)
and its [data](../../frontier/cover-geometry/proper_support_profile_residual.json)
pin Section7's actual-family data, check the literal conditional channel
containment, independently enumerate the support polynomials by set
partitions, and retain the384 positive limiting values. All971 explicit
checks pass, including the exact height-five outside-box consumer.
The endpoint-box proof and geometric cap sums above carry the unbounded
height claims; the sampled finite heights do not replace those proofs.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/proper_support_profile_residual.py
```

The [small-core producer](../../frontier/cover-geometry/small_actual_core_outside.py)
and [exact results](../../frontier/cover-geometry/small_actual_core_outside.json)
reconstruct the actual root regions and all240000 channel atoms at
heights2,3,4. All65 explicit checks pass, including the full Euler tail,
the successful height-three query and continuation, and the failed
height-two certificate. The unrestricted outside heights are handled by
the geometric sum and union bound, not by finite sampling.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/small_actual_core_outside.py
```

Section7 refutes universal success of the present IP1/IP3 certificate,
even within the rooted-plus-old-L inventory. Section8 repairs the stated
counterexample family and gives a finite-core sufficient class, but no
universal estimate for the residual event probabilities is established.
An arbitrary-family argument still needs a uniform actual-survival
estimate or another source with controlled complete-query numerator.
Bad fibres cannot be discarded
and nu3 renormalized without paying the changed root query law. Arbitrary
non-rooted supports remain an additional unresolved obligation.
There is also no reduction here from arbitrary prime sets to seven
coordinates. The unrestricted #7 goal remains open.
