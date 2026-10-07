[Index](../../../marked_head_profile.md) · [Actual surviving-fibre inequality](528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md) · [Same-law overlap certificates](../400-449/433-chordal-overlap-certificates-and-their-exact-finite-limits.md)

# An irredundant comb separates fibre credits from supported query laws

There is an explicit finite original family for every H>=405, supported on P={3,5,7,11,13,17,19}, with ternary height H and all other original heights at most3, for which the following obstruction holds. Fix every nonternary coordinate to normalized Haar on its full actual pure-prime survivor. For any ternary probability on the actual pure3 survivor, even allowing singular laws and arbitrary tails, let mu be the resulting product conditioned on the complete original survivor set. Then

    positive exact-single-class fibre estimate
        implies R_P(mu)>19H/694>565/51.                (IC1)

Here R_P(rho)=sum_(d>1,P-smooth) max_a rho(a mod d), including every query depth. The fibre estimate uses exact individual deletion probabilities, so neither sharper cylinder caps nor additional own-coordinate avoidance credits repair this failure. Every original class has a private integer; removing redundant originals cannot remove the example.

For the very same families, overlap accounting gives actual source survivor mass above1/10, and a different fixed nonternary product source gives

    R_P(nu)<1097/128<565/51,
    nu<720 H_P.                                      (IC2)

For each H this law is fixed before every query, and retains normalized Haar on the same actual pure3 survivor. Arbitrary additional originals touching23 or29, supported on P union{23,29}, leave full Haar survivor mass above2339/8110080>1/3500. Thus(IC1) is a failure of the specified source and its single-class mass estimate, not a failure of the seven-prime query target. No unrestricted Erdős#7 result is claimed. The construction and arbitrary-height arguments below are ordinary proofs; the finite rational constants and local separation facts have a separate exact verifier. Lean verification is limited to the explicitly scoped checks below.

## One fixed residue for every full numerical label

For a prime p, e>=1 and0<=a<=p-2, put

    C(p,e,a)=((a+1)p^(e-1)-1) mod p^e.

Its first e-1 base-p digits are p-1 and its next digit is a. These cylinders are pairwise disjoint as(e,a) varies: a shallower cylinder leaves the all-(p-1) branch before a deeper one, and different a at equal depth disagree there.

In the ternary coordinate define

    A_i=C(3,i,0),    T_i=C(3,i,1),
    Z_H=(-1) mod3^H,    W_H=union_(1<=i<=H)T_i.

The A_i, T_i and Z_H partition the ternary carrier. Write Q=P minus{3}. Include exactly one original for each numerical modulus

    m=3^i product_(q in Q)q^e_q>1,
    0<=i<=H,    0<=e_q<=3.

Let D={q:e_q>0}, k=|D|, and epsilon=0 when i=0 and1 otherwise. For k>=2 set

    gamma(q,k,epsilon)=min(2k-2+epsilon,q-2).

Assign the original coordinate residues as follows; the CRT then gives one fixed residue modulo the full m.

| Original label | Ternary condition | Nonternary conditions |
| --- | --- | --- |
| D empty, i>0 | A_i | none |
| i=0, k=1 | none | C(q,e_q,0) on the sole q |
| i>0, k=1 | T_i | C(q,e_q,1) on the sole q |
| i=0, k>=2 | none | C(q,e_q,gamma(q,k,0)) on every q in D |
| i>0, k>=2 | T_i | C(q,e_q,gamma(q,k,1)) on every q in D |

There are(H+1)4^6-1 originals, all with distinct odd numerical moduli greater than1. At H=405 this is1,662,975. This is an explicit family formula, not an enumeration of candidate covering systems.

## Every original has a private integer

For an original with nonternary support D, place every absent q-coordinate in(-1)mod q^3, and place the coordinates in D in their prescribed cylinders. Use ternary coordinate Z_H for i=0, T_i for i>0 with D nonempty, and A_i for a pure ternary original. These choices specify a nonempty CRT cylinder inside that original.

Any competing original with a nonternary coordinate outside D is excluded by the all-(q-1) prefix there. A pure ternary competitor is excluded by the disjoint ternary partition. For a mixed competitor with proper support E subset D and s=|E|>=2, take the largest prime q in E. If q has rank r in Q then r>=s and q-2>=2s. Consequently

    gamma(q,s,epsilon')<=2s-1,
    gamma(q,k,epsilon)>=2s when k>s.

The corresponding side cylinders are disjoint, regardless of the two exponent choices. A singleton competitor uses side0 or1, whereas mixed sides are at least2. With equal supports, the largest prime distinguishes epsilon=0 from epsilon=1; there is no clipping at that coordinate. With equal supports and epsilon, different exponent profiles are separated by the side-cylinder disjointness. Distinct positive ternary levels have disjoint T_i. Pure-coordinate cases follow from the same disjointness directly.

The proposed cylinder therefore meets no other original. Resolving it on the finite full period gives a private integer. In particular, the remaining mixed originals are still irredundant after the pure-coordinate and{3,q} deletions.

## Exact individual deletion still gives a negative fibre estimate

For q in Q define

    a_q=q^-1+q^-2+q^-3,    s_q=1-a_q,
    S_q=Z_q minus union_(e=1..3)C(q,e,0),
    lambda_q=H_q|S_q/s_q,    u_q=a_q/s_q.

The six u_q are

    (31/94,57/286,133/1198,183/2014,307/4606,381/6478).

For every allowed positive side a, lambda_q(C(q,e,a))=q^-e/s_q. Take any probability lambda3 supported on S3=W_H union Z_H and form the one product lambda=lambda3 tensor product_q lambda_q.

On T_i, only positive ternary level i is active. Its{3,q} blockers are union_(e=1..3)C(q,e,1), of lambda_q mass u_q. On Z_H there are no such blockers. Every remaining mixed original has sides at least2, disjoint from both side0 and side1. Its exact mass inside the pre-mixed surviving carrier is therefore

    product_(q in D)q^-e_q/s_q
       * integral_(I_m) product_(q not in D)(1-beta_q(t)) d lambda3(t).

Let FC_exact be the pre-mixed carrier mass minus the sum of these exact individual masses. The cylinder caps in report528 only increase each deletion charge, so its bare estimate satisfies FC<=FC_exact<=lambda(U). There is no uncounted own-coordinate avoidance improvement in FC_exact for this family.

Put

    g=product_q(1-u_q),
    h1=sum_q u_q product_(r!=q)(1-u_r).

On each T_i, every nonternary exponent profile with support size at least two has two active original labels, d and3^i d. On Z_H, only d is active. Summing all exponent choices gives the two exact integrands

    K=g-2 sum_(|D|>=2)u_D product_(q not in D)(1-u_q)
      =3g+2h1-2
      =-5263897225533641/276488459193698752<-19/1000,

    T=1-sum_(|D|>=2)u_D
      =2+sum_q u_q-product_q(1+u_q)
      =1303469977854414345/1935419214355891264<27/40.

For z=lambda3(Z_H),

    FC_exact=(1-z)K+zT<(-19+694z)/1000.                (IC3)

Each3^i d retains its actual T_i; no inventory is reused at a different depth. For normalized Haar on S3, z=2/(3^H+1). When H>=4 this is at most1/41, and(IC3) gives FC_exact<-17/8200<0.

## Every ternary reweighting with positive estimate concentrates the final law

Positive FC_exact in(IC3) forces z>19/694. Let V_w be the actual nonternary survivor over any T_i, and V_z the one over Z_H. The former has all restrictions of the latter, together with the{3,q} and positive-ternary mixed restrictions. Thus V_w subset V_z.

Both have positive product-lambda_q mass: placing every q-coordinate in(-1)mod q^3 avoids every displayed side cylinder. Write these masses as h_w and h_z, with0<h_w<=h_z. In particular lambda(U)>0 for every allowed lambda3, even when its FC estimate is negative. For mu=lambda|U/lambda(U),

    mu3(Z_H)=z h_z/((1-z)h_w+z h_z)>=z.

Each query cylinder(-1)mod3^i for1<=i<=H contains Z_H. Under this same final law,

    R_P(mu)>=sum_(i=1..H)mu3((-1)mod3^i)
            >=H mu3(Z_H)>=Hz>19H/694.                 (IC4)

At H=405 the surplus over565/51 is335/35394>0, proving(IC1) for all H>=405. This argument covers singular ternary laws and infinite query sums and uses no query stop-loss estimate. It excludes simultaneous positive FC_exact certification and the target response for the specified fixed nonternary sources. It does not exclude a good law obtained despite a negative FC_exact estimate.

## A different fixed product source meets the query target

Index Q increasingly as q_1,...,q_6. Define masks

    V_(q_r)=Z_(q_r) minus
          union_(e=1..3, a=0..2r-1)C(q_r,e,a).

These are allowed sides since2r-1<=q_r-2. Keep nu3 equal to normalized Haar on the actual pure3 survivor S3=W_H union Z_H, and take nu_(q_r) to be Haar conditioned on V_(q_r). For each H their product nu is chosen once, independently of every query. The six nonternary masks themselves do not depend on H.

The ternary support avoids every A_i. The masks exclude sides0 and1, so pure-q and{3,q} originals are avoided. For any mixed original with support size k>=2, choose its largest q_r. Since r>=k, its side is unclipped and

    gamma(q_r,k,epsilon)=2k-2+epsilon<=2r-1.

That coordinate excludes the original. Thus nu(U)=1 for every H, with all original labels and phases unchanged.

Its mask masses are1-2r a_(q_r)>1-2r/(q_r-1). Consequently

    sum_(e>=1)max_b nu_(q_r)(b mod q_r^e)
       <=1/[(q_r-1)(1-2r a_(q_r))]
       <1/(q_r-1-2r).

In prime order the final bounds are1/2,1/2,1/4,1/4,1/6,1/6. The pure3 survivor has Haar mass(1+3^-H)/2 and contains the entire T_1 cylinder. Thus its maximum cylinder probability at every positive depth e is2*3^-e/(1+3^-H), including depths above H, and R3(nu3)=1/(1+3^-H)<1. This is an actual product law, so the complete query inventory factors:

    1+R_P(nu)<2(3/2)^2(5/4)^2(7/6)^2=1225/128.

Each entire first-digit cylinder2r remains in V_(q_r), so the unrounded cylinder cap q^-e/(1-2r a_(q_r)) is attained at every depth. The retained data also give the unrounded uniform query upper bound2*product_q(1+1/[(q-1)H_q(V_q)])-1; the simpler bound above suffices for the continuation.

This proves(IC2), with query surplus565/51-1097/128=16373/6528. All deeper query tails are included. For H>=4, this uses the very same ternary marginal that made the original FC_exact estimate negative; only the nonternary source has changed. The same law has full Haar density less than

    2 product_(r=1..6)(q_r-1)/(q_r-1-2r)=720.

For any finite additional family supported on P union{23,29} and touching23 or29, each full numerical label is uniquely d23^j29^k with j+k>0. Under nu tensor H23 tensor H29, their one actual forbidden union has mass less than(51/616)(1225/128), regardless of all their original phases and heights. Hence remaining probability is greater than2339/11264, and full Haar survivor mass is greater than2339/8110080>1/3500.

## Coherent overlap also repairs the original source's mass estimate

On T_i, normalize the pre-mixed nonternary carrier after the side1 deletions. This is a product law. For each fixed k>=2 and epsilon in{0,1}, define a q-event by membership in union_(e=1..3)C(q,e,gamma(q,k,epsilon)). Across q these events are independent, each of probability

    v_q=u_q/(1-u_q).

The union of the actual originals in this(k,epsilon) group is exactly the event that at least k of the six q-events occur. Indeed any k successful coordinates select one present support and its uniquely determined exponent profile; conversely a class in the group supplies k successes. Different groups need not be independent.

Let N be a sum of independent Bernoulli variables with probabilities v_q. Applying a union bound between groups, after exactly accounting for overlap within each group, gives

    h_w>=g[1-2 sum_(k=2..6)Pr(N>=k)]
        =g[1-2 E(N-1)_+]
        =g[3-2 sum_q v_q-2 product_q(1-v_q)]
        =204550887415385513/1935419214355891264>1/10.

Over Z_H only epsilon=0 is active, and there is no side1 deletion. The same calculation with probabilities u_q gives

    h_z>=2-sum_q u_q-product_q(1-u_q)
        =1475883367641688121/1935419214355891264>3/4.

Integrating proves lambda(U)>1/10 for every H>=1 and every allowed lambda3. Thus a negative exact-single-class estimate coexists with uniformly positive actual mass. The missing term is overlap between genuinely different, irredundant originals. The common phases indexed by(k,epsilon) permit its calculation here; arbitrary originals are not assumed to admit this grouping.

## Verification and remaining interface

The [exact verifier](../../../frontier/cover-geometry/fibre-credit-irredundant-comb/fibre_credit_irredundant_comb.py) checks the displayed rational constants, side-cylinder disjointness at the nonternary cutoff, proper-support and equal-support phase separation, and every largest-coordinate mask condition. Its [result](../../../frontier/cover-geometry/fibre-credit-irredundant-comb/fibre_credit_irredundant_comb.json) retains these finite facts. Run:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-irredundant-comb/fibre_credit_irredundant_comb.py
```

The program does not enumerate the full original CRT period or claim that a bounded sample proves the arbitrary-H statements. Those follow from the disjoint side-cylinder construction, the exact two-fibre identity and the conditioning argument above. Default execution checks the retained result; `--output PATH` writes the recomputed result. No source geometry or Lean build is used.

For arbitrary originals, report433 already supplies same-law forest and chordal overlap certificates with actual intersection masses; no new forest theorem is needed. The unresolved step is a sufficiently strong estimate of actual overlapping deletions, or a supported source change, that also controls the full query inventory for unrestricted original phases and heights. The two repairs here are verified for this explicit family, not for every seven-prime core.

## Actual ternary-height-one families realize the single-class fibre charges

The side-comb construction also applies at ternary height one, with arbitrary
finite nonternary heights and any specified two-root partition. It realizes
all the individual charges in
[Report528's finite-height comparison](528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md#finite-height-profiles-do-not-extend-this-fibre-comparison-to-eleven-primes)
simultaneously. This is an actual finite irredundant NONCOVER: the negative
quantity is the carrier mass minus a sum of individual deletion masses, not
the actual survivor mass. The construction reuses the side cylinders and
private-cylinder separation proved above.

Let Q be any finite set of primes at least5, with positive finite heights
h_q, and partition Q=A disjoint union B. Include exactly every nonunit
divisor of `3*product_q q^h_q`. Using the same `C(q,e,a)` as above, give the
originals the following globally fixed CRT phases:

| Numerical label | Ternary phase | Nonternary side cylinders |
|---|---|---|
|3|0|none|
|`q^e`|none|`C(q,e,0)`|
|`3q^e`|1 if `q in A`, otherwise2|`C(q,e,1)`|
|`3^epsilon*d`, `D=supp(d)`, `k=|D|>=2`|none for epsilon0; one fixed `r_D in{1,2}` for epsilon1|`C(q,v_q(d),min(2k-2+epsilon,q-2))`, `q in D`|

The roots `r_D` may depend on the support D but are chosen once. Numerical
labels are distinct and the palette is divisor-closed. Every original has
a private CRT cylinder. Put each absent q-coordinate on the tail
`(-1) mod q^h_q`, and each present one in its prescribed side cylinder.
Use root0 for pure3, the original root for a3-divisible label, and any
retained root for a3-free label.

A competitor using an absent coordinate misses the tail. Singleton
competitors use sides0 or1, while support size at least two uses sides at
least2. For a proper competing support E of size s>=2, its largest prime q
has rank at least s among primes starting at5, so `q-2>=2s`: its side is at
most `2s-1`, while the target's is at least `2s`. For equal supports, the
largest prime separates epsilon0 and epsilon1 by the unclipped sides
`2k-2` and `2k-1`. With equal support and epsilon, different exponent
profiles are separated by side-cylinder disjointness. These cases exhaust
competitors, independently of the support-dependent ternary-root choices.

Thus the actual family is irredundant and comparable-disjoint. Either
retained ternary root together with all nonternary tails survives, so it
does not cover. Its full original period is finite.

Put

    a_q=sum_(e=1..h_q)q^-e, s_q=1-a_q,
    c_q=1/s_q, b_q=a_q/s_q.

Under the actual pure-conditioned nonternary product law, all side1
blockers have exact total mass b_q on their assigned ternary root. Hence
beta is the exact partition endpoint, without artificial enlargement.
Every remaining mixed original uses sides at least2, disjoint on its own
coordinates from both pure and side1 deletions. Its exact mass on root r
inside the post-star carrier is

    product_(q in D)c_q*q^(-v_q(d)) * g_r(D),
    g_r(D)=product_(q notin D)(1-beta_qr).

For one FIXED root weight `w in[0,1]`, choose `r_D` maximizing
`w*g_1(D)` and `(1-w)*g_2(D)`. Summing the actual exponent inventory
then makes the carrier mass minus the sum of the exact individual mixed
deletion masses equal to `F_h(A,w)` in Report528. Their union has mass at
most that sum; strict inequality is not asserted for every finite Q.
In the negative eleven-prime instance below, the sum exceeds the carrier
mass and hence strictly exceeds the deletion union. The subtraction there
is therefore not the actual survivor mass.

At the eleven-prime profile of Report528, take `A={5}` and `w=1/2`.
The already retained exact comparison is negative. The present family
realizes it as this exact-single-class subtraction, on the palette of
`2*6^2*5^5*4^3-1=14399999` original labels specified by the formula.
No enumeration of that palette or its CRT period is needed. For each
fixed w the construction gives a corresponding actual family; it does
not assert that one family realizes the maxima for every w.

This excludes a uniform repair based only on sharper individual cylinder
caps, their own-coordinate avoidance, or nonrealizability of the partition
endpoint under finite heights, divisor closure and irredundancy. It does
not exclude stronger joint-intersection estimates or global-extremality
constraints. In fact this comb fails an existing repair test: its originals
`14593 mod15015`, `14593 mod19635` and `1888 mod21945` all have phase
`103 mod105`. [Report385's phase-capacity consumer](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#17-small-interfaces-bound-whole-cover-numerical-inventories)
forbids three such originals in a globally extremal whole cover with
ternary height one. The comb is not asserted to satisfy that premise.

These are ordinary construction and measure calculations. The negative
FC value is reused from Report528's existing exact result; no duplicate
FC consumer or new Lean verification is added.

## Eight-prime combs refute a uniform relative Haar reserve

The same side-comb construction gives actual finite counterexamples to

    H(U) >= (1/6) H(V3 x W),                                   (RR1)

where V3 avoids all actual pure ternary originals, W avoids all actual
3-free originals, and U avoids the complete actual family. Here H is one
product Haar probability throughout. The counterexamples remain
divisor-closed and every original has a private CRT cylinder. They do not
assume whole-cover cardinality or modulus-sum minimality.

Use the first eight odd primes and put

    Q={5,7,11,13,17,19,23}.

Include every numerical modulus

    m=3^i product_(q in Q)q^e_q >1,
    0<=i<=H, 0<=e_q<=3,

with EXACTLY the fixed CRT phases of the construction above: pure ternary
classes use A_i; pure q-classes use side0; mixed singleton classes use T_i
and side1; a nonternary support of size k>=2 uses

    gamma(q,k,epsilon)=min(2k-2+epsilon,q-2),
    epsilon=0 for i=0, epsilon=1 for i>0,

and T_i when i>0. The exponent vector uniquely determines its numerical
modulus, so there are(H+1)4^7-1 distinct odd nonunit originals. These are
one actual family for each H, with no phase choices depending on the
subsequent source or query. The private-cylinder proof above still applies:
the seven increasing q_r satisfy q_r-2>=2r. Thus the example does not rely
on removable originals.

### Count the full surviving sets on one common period

At q, each side a in{0,...,q-2} is the disjoint union of C(q,e,a) for
e=1,2,3. On the q^3 window it has exactly q^2+q+1 residues. All sides are
disjoint, and the terminal all-(q-1) prefix has one residue. Removing the
pure side0 therefore leaves q^3-q^2-q-1 residues.

Let V_z be the complete nonternary survivor of all i=0 originals, including
the pure q originals. Let V_w additionally avoid side1 on every coordinate
and every mixed support with epsilon=1. The exact full-survivor identity is

    U = (union_(i=1..H) T_i) x V_w  disjoint-union  Z_H x V_z,
    V3 x W = (union_(i=1..H) T_i union Z_H) x V_z.               (RR2)

Thus W=V_z. Both V_z and V_w contain the common terminal cylinder. In the
common Q-period, the integer counts are

    Q0=product_(q in Q)q^3=51404758182902197698625,
    N_pure=product_(q in Q)(q^3-q^2-q-1)
          =22477958755529321140096,
    N_z=|V_z|=16540311957403355160121,
    N_w=|V_w|=2569696844461203895339.                            (RR3)

These count complete surviving fibres, not a selected product subset.
To obtain them without enumerating Q0, retain the side value or terminal
value on each coordinate. At a support of size k, a forbidden mixed
rectangle is present precisely when those k sides equal their prescribed
gamma values. Equivalently the union over all k-supports is the event that
at least k such side matches occur. The exponent choices have all been
included: a nonterminal side determines its unique depth e<=3.

Weighted variable elimination now counts the avoidance of those actual
rectangles. A side has weight q^2+q+1 and a terminal has weight1. A
partially matched rectangle is discarded when a processed coordinate
disagrees, and rejects the entire fibre when all its coordinates match.
Branches with the same remaining rectangles can be combined by adding
their integer weights. This recurrence preserves the full weighted
Cartesian count. It does not multiply avoidance probabilities of groups
sharing coordinates.

In the ternary3^H window, the union of T_i has(3^H-1)/2 residues and
Z_H has one. Hence the full counts in period L=3^H Q0 are

    u=|U mod L|=((3^H-1)/2)N_w+N_z,
    m=|(V3 x W) mod L|=((3^H+1)/2)N_z.                        (RR4)

For H=5, the98,303-original family has

    u=327473630137209026496140,
    m=2017918058803209329534762,
    6u-m=-53076277979955170557922<0,
    H(U)/H(V3 x W)
      =163736815068604513248070/1008959029401604664767381
      =0.1622829176381065...<1/6.                              (RR5)

For H=6, the114,687-original family has

    u=951909963341281573063517,
    m=6037213864452224633444165,
    u/m=0.1576737191548292...
       <21876797/136331397<1/6.                               (RR6)

The smaller threshold is the sufficient reserve for the comparison
1+(2A-1)/delta<28 with A=13463054/5049311 from
[Report563's seven-prime companion](../550-599/563-prefix-free-rooted-labels-admit-all-later-four-mixed-towers.md#mixed-ternary-label-gaps-give-an-eight-prime-source).
Consequently neither a universal1/6 reserve nor that weaker strict
threshold is valid for every actual family. This does not establish a
lower bound on the actual Haar query norm; it refutes the proposed
uniform reserve used to feed that particular comparison.

### The same families still have an inexpensive complete-query source

The existing product-source repair above extends directly to seven
nonternary coordinates. At q_r, avoid sides0,...,2r-1 at depths1,2,3,
and use normalized Haar on the remaining V_(q_r). Its mass is

    H_q(V_(q_r))=1-2r(q_r^-1+q_r^-2+q_r^-3)
               >1-2r/(q_r-1)>0.

Use normalized Haar on V3 for the ternary factor. Every actual original
is avoided: for a support of size k, its largest prime has rank r>=k and
its selected side is at most2k-1<=2r-1. Pure and mixed singleton originals
are excluded by sides0 and1, and the ternary pure originals by V3.

For this ONE product law nu, every numerical query and every height obeys

    B_(P8)(nu)
      <2 product_(r=1..7)(1+1/(q_r-1-2r))
       =(1225/128)(9/8)=11025/1024<28.                        (RR7)

The ternary factor uses H(V3)>1/2 and the complete geometric series;
each nonternary factor uses the displayed actual mass. Thus the relative
Haar-reserve failure coexists with a good source on the SAME full
survivor. It is not a counterexample to the existential source target or
to unrestricted Erdős#7.

The exact [consumer](../../../frontier/cover-geometry/fibre-credit-irredundant-comb/relative_comb_reserve.py)
and [results](../../../frontier/cover-geometry/fibre-credit-irredundant-comb/relative_comb_reserve.json)
reconstruct local side cylinders, count both full nonternary fibres, and
verify every numerical original label in the finite H=4,5,6 controls.
The H=4 control remains above1/6. The source and phase definitions,
not a list of independently selected residues, determine the entire
family in each case.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-irredundant-comb/relative_comb_reserve.py
```

A scoped Lean check verifies the finite inventory arithmetic, the common
fibre-mixture identity, both strict reserve refutations, and the same-family
product budget. Its six declarations use only the standard axiom set.
The actual CRT construction and weighted full-fibre enumeration remain
the ordinary argument and exact consumer; no complete formal measure
theorem or new canonical wrapper is claimed.

## Low projection avoidance permits arbitrary higher phases

The RR7 source also handles finite families whose high ternary layers do
not have the comb phases. Keep P8={3,5,7,11,13,17,19,23} and Q=P8 minus{3}.
For a probability eta on the Q-adic carrier, write

    q_n(eta)=max_a eta(a mod n),
    beta=B_Q(eta)=sum_(n Q-smooth, including1) q_n(eta)<infinity.

This is the complete query norm: absent original labels and every query
height are included, and q_1=1. Fix h>=1 and one finite family of distinct
nonunit P8-smooth numerical moduli with globally fixed residues. Write
each original as m=3^j n, where n is Q-smooth, and let J_m be its actual
cofactor cylinder. Assume ONE eta satisfies

    eta(J_m)=0 for every original with j<=h and n>1.           (HP1)

This includes every ternary-free original(j=0). It imposes no condition
on the phases or heights of pure ternary originals, or on any original
with j>h. Under beta<3^h+1, there is one probability nu avoiding the whole
original family and satisfying

    B_(P8)(nu)<=1+(2 beta-1)/(1-(beta-1)/3^h).                (HP2)

To prove this, condition ternary Haar on avoidance of ALL pure ternary
originals. Distinct numerical moduli supply at most one forbidden class
per positive depth, and finiteness gives a removed mass strictly below
sum_(j>=1)3^-j=1/2. The resulting rho_3 therefore has

    max_a rho_3(a mod3^j)<=2/3^j (j>=1),   B_{3}(rho_3)<=2.

Use the fixed product law rho=rho_3 times eta. It avoids every pure
ternary original and, by HP1, every remaining original at j<=h. Its
complete query norm is at most2 beta. Let D be the union of the remaining
original cylinders, necessarily j>h and n>1. For each pair(j,n), there
is at most one original phase, because the original numerical moduli are
distinct. The union bound and the product law give

    rho(D)<=sum_(j>h,n>1) (2/3^j) q_n(eta)
           =(beta-1)/3^h.                                  (HP3)

The subtracted unit1 is essential: pure ternary originals were already
removed. This is a union bound, with no independence assertion between
overlapping original events. The bound sums every cofactor query label,
so it also covers any finite selection of higher original heights.

Since HP3 is less than1, condition rho once on the complement of D.
For each nonunit numerical query, its maximum mass increases by at most
the reciprocal of that SAME reserve. Summing these nonnegative bounds
over all queries gives HP2; the unit query of the conditioned probability
still contributes exactly1. The source is fixed before any query is
chosen. The ternary-height sums are convergent geometric series; the
cofactor sum is the assumed finite complete norm beta. Nonnegative
summation justifies the full-query bound, without replacing the complete
norm with the list of original labels.

### The first two ternary layers suffice for the comb masks

Take eta to be the RR7 nonternary product law: at the r-th prime q_r in Q,
exclude sides0,...,2r-1 at depths1,2,3, then normalize Haar. It satisfies

    beta<beta_0=product_(r=1..7)(1+1/(q_r-1-2r))
               =11025/2048.

For the low nonpure inventory, retain any original projections null
under these masks. In particular, the comb projections at j=0,1,2
satisfy HP1 by the largest-prime argument used for RR7. Pure ternary
originals may have arbitrary fixed phases at every height. Every mixed
original at j>=3 may now have an arbitrary fixed phase and arbitrary
Q-smooth cofactor, with no cofactor-height cap; numerical moduli must
remain distinct. Using beta_0 in both nonnegative debit and query bounds
yields

    rho(not D)>=9455/18432>0,
    B_(P8)(nu)<=189473/9455<28.                              (HP4)

More generally, at h=2 the right side of HP2 is below28 precisely when
beta<31/5, within its positive-reserve domain. If HP1 holds through h=4,
the same argument gives the stronger reserve and complete-query bounds

    rho(not D)>=156911/165888,
    B_(P8)(nu)<=1777073/156911<12.                           (HP5)

The beta_0 debit at h=1 exceeds1, so this estimate gives no conclusion
there. HP1 has not been established for arbitrary P8 families. HP4 and
HP5 extend the admitted phase inventory under a stated low-projection
condition; they do not prove the unrestricted source target or Erdős#7.

The existing exact consumer also checks HP4, HP5 and the height-two
threshold. A scoped Lean application verifies the finite conditioning
implication from explicit loss and aggregate-query hypotheses, together
with the HP4 and HP5 reserve and budget fractions, using only the standard
three axioms. The threshold value31/5 is checked by the exact consumer;
its equivalence follows from the displayed positive-reserve inequality.
The arithmetic construction supplying those hypotheses and the complete
infinite query sums are the ordinary proof above, not a fully formalized
source theorem. The Lean application reuses existing probability results
and introduces no canonical wrapper module.

## Requiring all low projections to vanish has an unbounded cost

HP1 cannot be imposed as a universal inexpensive-source selection rule,
even when the ternary height is only two and the Q law may be arbitrarily
correlated. The following actual family has that obstruction and still
admits a uniformly inexpensive joint source.

Fix H>=1, use the side cylinders C(p,e,a) above, and put
T_p=[-1]_(p^H). For each j=0,1,2 take the following originals. An entry
with cofactor n has numerical modulus3^j n; when j>0 its ternary phase
is1 modulo3^j, and when j=0 it has no ternary condition.

| Cofactor | Range | Fixed cofactor projection at ternary depth j |
| --- | --- | --- |
| 5^e | 1<=e<=H | C(5,e,j) |
| 7^f | 1<=f<=H | C(7,f,j) |
| 5^e 7^f | 1<=e,f<=H | C(5,e,3) times C(7,f,3+j) |

CRT specifies one fixed residue per original. The exponent triples are
distinct, so these are3(H^2+2H) distinct odd nonunit moduli. Their ternary
height stays two as H grows. Each original has a private CRT cylinder:
for a pure-cofactor original put the other cofactor coordinate in its
tail T_p; for a mixed-cofactor original use its two prescribed sides.
Different departure depths or sides exclude every competing projection.
Choose the prescribed ternary phase when j>0 and root0 when j=0. Thus
the obstruction does not depend on redundant originals.

Suppose a Q probability eta assigns zero mass to every displayed
projection. Avoiding the pure-cofactor projections leaves

    S5=T5 disjoint-union A5,  A5=union_(1<=e<=H) C(5,e,3),
    S7=T7 disjoint-union A7,  A7=union_(1<=f<=H,a=3,4,5) C(7,f,a).

The mixed projections have union A5 times A7. Hence their common
survivor, with all other Q coordinates free, is exactly

    V_H=(T5 times S7) union (S5 times T7).                   (LP1)

The two rectangles may overlap. Since the inventory is finite,
eta(V_H)=1 and eta(T5)+eta(T7)>=1. For each e=1,...,H, the query
[-1]_(5^e) contains T5, and [-1]_(7^e) contains T7. These2H numerical
queries are distinct. Monotonicity, the unit query and nonnegativity give

    B_Q(eta)>=1+H(eta(T5)+eta(T7))>=H+1.                     (LP2)

This holds for every such eta, with no product, density or prescribed
marginal assumption, and also when its norm is infinite. Auxiliary
restrictions cannot remove the lower bound. At H=6 the144-original
family forces beta>=7, excluding the beta<31/5 input for HP4.

More strongly, any joint P8 law whose Q marginal satisfies this same
low-projection-null condition has B_(P8)>=B_Q>=H+1, regardless of its
ternary conditionals. At H=27 this excludes B_(P8)<28 for the entire
low-null class, on an actual2349-original family of ternary height two.

### Retaining ternary activation removes this obstruction

On the SAME actual family, take normalized Haar on ternary root0,
5-adic root1 and7-adic root1, and independent Haar on the other P8
coordinates. Every j=1,2 original is inactive on ternary root0. At j=0,
the pure-cofactor side0 classes have first root0 or p-1, excluded by
root1. Every mixed j=0 original has5-side3, whose first root is3 or4,
also excluded. Thus this one product law avoids the full original family
for every H.

A normalized Haar law on one p-root has complete query norm
1+p/(p-1); free Haar has norm p/(p-1). Consequently this supported law
has the exact all-height norm

    B_(P8)=(5/2)(9/4)(13/6)
           product_(p=11,13,17,19,23) p/(p-1)
          =1255501/73728<28.                                (LP3)

It does not satisfy HP1: for example, the cofactor projection of the
modulus15 original is[1]_5 and has marginal probability1. Its ternary
activation is absent, so the actual original still has probability0.
LP2 therefore refutes the blanket low-null strategy, not the unrestricted
joint-source target. A general source construction cannot uniformly
replace actual originals by unconditional avoidance of all their low
cofactor projections; the ternary activation remains relevant.

[Report536](536-ternary-conditioning-preserves-a-joint-query-and-entropy-boundary.md)
already exhibits higher projected multiplicity on a chosen ternary
fibre. LP2 additionally bounds EVERY law avoiding all low projections,
while keeping ternary height two; it does not prescribe the marginal
whose cost is being bounded. The side-cylinder partition and probability
inequalities are reused, with no claim of a new general measure theorem.

The existing consumer reconstructs the actual CRT labels, verifies one
private point per original, the exact projected survivor and the entire
cheap-source support at H=1,2. The controls have9 and24 originals and
projected survivor counts5 and31. These controls do not prove the
arbitrary-H statement. A scoped Lean application checks, for every finite
radix-word height and every rational law on the projection survivor, the
first-departure argument, the tail-union inclusion and the H+1 finite
prefix-query lower bound, together with the H=6 contradiction and LP3's
rational product. Numerical CRT transport and the infinite Haar-tail
interpretation remain the ordinary proof above. No unrestricted Erdős#7
conclusion follows from this method obstruction.

## A selected ternary root needs only its active low projections

There is a positive source condition that permits the LP family and
arbitrary higher mixed additions without imposing HP1. Keep a finite
distinct nonunit P8-smooth family with fixed phases. Choose a ternary
root r that is not forbidden by an actual modulus3 original. For each
nonunit Q-smooth cofactor n, collect the complete mod-n phases of

- its j=0 original, if present;
- its j=1,2 originals whose first ternary root is r, if present.

Assume this set has at most ONE distinct phase for every n. Identical
phases may be merged; phases attached to other ternary roots are not
included. The condition concerns each complete numerical cofactor,
not merely its prime support. It places no restriction on higher mixed
phases or heights, and permits all pure ternary originals except a
modulus3 class forbidding the selected root.

The merged inventory is a finite distinct nonunit Q-smooth family.
Apply [Report563 MT11](../550-599/563-prefix-free-rooted-labels-admit-all-later-four-mixed-towers.md#83-a-seven-prime-companion-and-the-remaining-boundary)
directly to obtain ONE cofactor law eta avoiding it, with complete norm

    beta=B_Q(eta)<=A=13463054/5049311.                       (AR1)

In root r, remove every actual pure ternary original and normalize Haar
on what remains. Its unnormalized Haar mass is strictly greater than
1/3-sum_(j>=2)3^-j=1/6, because there is at most one original per depth
and the family is finite. This gives a law u with

    q_3(u)=1,  q_(3^j)(u)<=6/3^j (j>=2),  B_{3}(u)<=3.

The fixed product rho=u times eta avoids every pure ternary original
and every nonpure original at j<=2: each is either inactive on r or
has its cofactor phase excluded by eta. Only mixed originals with
j>=3,n>1 remain. Numerical distinctness and the same-law union bound give

    rho(D)<=sum_(j>=3,n>1)(6/3^j)q_n(eta)=(beta-1)/3,
    B_(P8)(rho)<=3 beta.

As before, n=1 is omitted only because all pure ternary originals were
already removed. Since beta<=A<4, condition rho once on avoidance of D.
Including the unit exactly once yields a law nu avoiding the whole family:

    B_(P8)(nu)<=1+(3 beta-1)/(1-(beta-1)/3)
               =(1+8 beta)/(4-beta)
               <=37584581/2244730<28.                       (AR2)

The reserve at A is2244730/5049311>0. On beta<4, the displayed budget is
below28 exactly when beta<37/12. All query labels and heights remain
included; eta and the final conditioning event are fixed before queries.

For the LP family, choose root0. Its j=1,2 originals all have root1,
so each active cofactor contributes only its j=0 phase. The condition
continues to hold after arbitrary finite mixed additions at j>=3 and
arbitrary higher pure ternary additions. If a modulus3 original is also
added, at least one of roots0 and2 remains available, and either has the
same inactive j=1,2 inventory. Thus these families admit the AR2 source
even where every all-low-projection-null law has cost at least H+1.

AR1 is an application of the existing seven-prime source, not a new
source theorem. The active-phase condition has not been proved for an
arbitrary P8 family. The exact consumer checks the resulting fractions;
a scoped Lean application verifies the finite conditioning implication
from its explicit deletion/query bounds and the rational threshold.
The root-conditioned Haar source, the MT11 measure application and
the complete infinite query sums remain ordinary mathematics here.

## An extra five-root guard obstructs the shared scalar estimate

The active-root argument leaves a source-design question when different
available ternary roots have incompatible low inventories. One possible
restriction is to require every cofactor point to leave an entire first
ternary root unblocked. The following finite example limits that
restriction when its source is evaluated by the same scalar weight for
mixed events and queries. It does not limit arbitrary supported joint
laws or every consumer of a full prefix-cap profile.

Keep Q={5,7,11,13,17,19,23}. Permit at most one actual pure class at each
nonunit pure numerical label, and add one auxiliary forbidden first
5-root different from the actual modulus5 phase. Three first roots
remain. In any one of them, all higher pure5 holes remove Haar mass at
most sum_(j>=2)5^-j=1/20, so each retains at least3/20. Assigning each
surviving root mass1/3 and normalizing Haar within it gives ONE law with

    k5(1)=1/3,  k5(j)<=20/(9*5^j) for j>=2,
    sum_(j>=1)k5(j)<=4/9.                                  (FG1)

Normalized Haar on the complete pure5 survivor instead has normalization
mass at least11/20, first-depth cap4/11 and total cap5/11. These are
simultaneous caps under each specified law, not separately optimized
marginals. Other prime directions retain the existing caps1/(p-2).

### The inherited consumer needs a smaller shared weight

Use a pure5 total t both as its event-inventory weight and as its query
weight in the support polynomial of Report563. Let rho_t be that
polynomial and N_t its complete query numerator, including the unit.
Direct reuse of the existing polynomial and numerator gives

    (37/12)rho_t(Q)-N_t
       =(35597719-81525298t)/31808700.                      (FG2)

Both expressions are affine in t: each polynomial term contains a
coordinate at most once, and the query support is disjoint from its
complementary polynomial. Thus, whenever the polynomial certificate is
positive, its complete-query estimate is below37/12 exactly when

    t<tcrit=35597719/81525298.                              (FG3)

The value37/12 is the sufficient cofactor threshold of AR2. It is a
threshold for this certificate, not a lower bound on the best possible
joint-source norm. All induced subset polynomials are positive for the
two reference profiles, but their resulting upper bounds both exceed it:

| Pure5 total t | rho_t(Q) | Complete-query upper bound | 37/12 minus the bound |
| --- | --- | --- | --- |
| 5/11 | 489631/883575 | 51157586/16157823 | -1783509/21543764 |
| 4/9 | 2676139/4771305 | 41733953/13380695 | -5721721/160568340 |

Clipping individual query bounds at1 does not improve either estimate.
For each of the127 nonempty prime supports, its largest bound occurs
when every selected exponent is1; the coordinate caps decrease at
higher exponents. The largest of these127 values occurs at label5 and
is9088732/16157823 for the Haar profile, or6816549/13380695 for the
balanced profile. Both are below1. The unit already contributes exactly1.
These254 finite checks exclude this clipping correction for the two
profiles, without excluding other joint inequalities between queries.

### A four-depth obstruction for every law on the auxiliary support

Consider the five forbidden prefixes

    0 mod5, 1 mod5, 2 mod25, 7 mod125, 32 mod625.            (FG4)

They are pairwise disjoint. The first two include one auxiliary guard;
FG4 is not an actual distinct-modulus original family. Let lambda be
any probability supported outside these prefixes. Write q_m for its
largest mod-m class mass, M=q_5, and c=lambda([2]_5). Roots2,3,4 carry
all mass, hence M>=1/3 and c>=1-2M. Inside root2, the numbers of available
prefixes at moduli25,125,625 are respectively

    5-1=4,  25-5-1=19,  125-25-5-1=94.                    (FG5)

These are counts of actual compatible prefixes, including every hole
visible at that depth. Consequently c<=4q_25, c<=19q_125 and
c<=94q_625, all for the SAME lambda. Set S=1/4+1/19+1/94=1119/3572.
Then

    q_5+q_25+q_125+q_625
      >=M+cS>=S+(1-2S)M
      >=S+(1-2S)/3=4691/10716,
    4691/10716-tcrit=485008057/436812546684>0.              (FG6)

Here1-2S=667/1786>0, so the direction is preserved even when1-2M
is negative. Every simultaneous prefix-cap profile on this auxiliary
support already exceeds tcrit in its first four layers. Improving the
pure law therefore cannot meet FG3 while retaining this shared scalar
consumer. No optimization or joint attainability of separate maxima is
assumed in FG6.

### The actual family and the additional restriction

The source-design situation occurs in the actual fixed-phase family

    2 mod3, 0 mod5, 6 mod15, 1 mod45,
    2 mod25, 7 mod125, 32 mod625.                           (FG7)

Its seven odd nonunit numerical moduli are distinct. Root2 modulo3 is
forbidden. The modulus15 original is active in ternary root0 and the
modulus45 original in root1; both project to1 mod5. A construction that
requires a whole first ternary root to be unblocked at each cofactor
point therefore adds the auxiliary guard1 mod5. Together with the
actual pure5 originals, this yields FG4.

That guard is stronger than avoiding FG7. At cofactor phase1 mod5,
the modulus45 original blocks only ternary phase1 mod9 inside root1;
phases4 and7 mod9 remain available. A joint or leaf-sensitive source
can use them without excluding the whole cofactor root. Thus FG6
obstructs this auxiliary-source shared-scalar route, not the actual
complete-query target B_(P8)<28 or Erdős#7. Separate event/query weights,
a consumer retaining the full profile, or adaptive within-root laws
require their own estimates and are not ruled out.

The existing exact consumer imports `support_polynomials` and
`query_numerator` from `mixed_tower_inventory.py`; it does not implement
a second polynomial recurrence. It records FG2, both reference profiles,
all254 clipping checks, the actual seven labels, and the finite625
survivor with the4,19,94 projection counts. A scoped Lean application
verifies FG6 and its strict comparison with FG3 for every rational
probability law on that explicit finite survivor subtype. It derives
the mass inequalities from actual pushforward laws and finite counts,
with only the standard three axioms and no scalar assumptions. This
finite rational verification does not formalize arbitrary real or
infinite laws, the polynomial consumer, or the actual-to-auxiliary
selection rule; those arguments are given above. It adds no frozen
wrapper declaration. The existing general prefix-capacity realization
result supplies no way around FG6: the obstruction holds for every
law on the stated support, irrespective of its construction.

## A depth-two leaf supplies a conditional source for the actual family

The active-root argument AR2 also has a leaf version. Keep a finite
distinct nonunit P8-smooth family with globally fixed original phases,
where P8={3,5,7,11,13,17,19,23} and Q=P8 minus{3}. Choose r mod9 whose
leaf avoids every actual pure modulus3 and modulus9 original. For each
complete nonunit Q-smooth numerical cofactor n, collect the full mod-n
phases of its j=0 original and all originals3^j n at j=1,2,3 whose
ternary cylinders intersect the leaf. Require at most ONE distinct
phase in this collection. Equal phases may be merged; inactive
originals are omitted. Intersection means agreement modulo3^min(j,2).
This condition concerns complete cofactor residues, not prime supports.

The merged collection is a finite distinct nonunit Q-smooth family,
so [Report563 MT11](../550-599/563-prefix-free-rooted-labels-admit-all-later-four-mixed-towers.md#83-a-seven-prime-companion-and-the-remaining-boundary)
provides ONE law eta avoiding it, with

    1<=beta=B_Q(eta)<=A=13463054/5049311.                    (AL1)

Normalize ternary Haar on the selected leaf after removing every
actual pure ternary original. Pure depths1,2 are already inactive.
At most one original occurs at each higher numerical power, and the
family is finite, so the retained unnormalized mass is strictly above

    1/9-sum_(j>=3)3^-j=1/18.

The resulting single law u simultaneously satisfies

    q_3(u)=q_9(u)=1,
    q_(3^j)(u)<=18/3^j for j>=3,
    B_{3}(u)<=1+1+1+18 sum_(j>=3)3^-j=4.                  (AL2)

On the fixed product rho=u times eta, every pure original and every
nonpure original through j=3 is null: the latter is either inactive
on the leaf or has its full cofactor phase excluded by eta. Only mixed
originals j>=4,n>1 remain. Numerical distinctness gives at most one
original per pair(j,n). Thus their actual union D obeys

    rho(D)<=18 sum_(j>=4)3^-j sum_(n>1)q_n(eta)
           =(beta-1)/3,
    B_(P8)(rho)<=4 beta.

The unit cofactor is omitted from the deletion sum because pure
ternary originals are already avoided. It remains in the complete
query norm. Since beta<4, condition this product once on avoidance of
D. The unit query stays exactly1, giving one complete survivor law nu:

    B_(P8)(nu)<=1+(4 beta-1)/(1-(beta-1)/3)
               =(1+11 beta)/(4-beta)
               <=10209527/448946<28.                       (AL3)

The expression increases on beta<4 and is below28 exactly when
beta<37/13. At A the reserve is2244730/5049311, and the gap from28
is2360961/448946. The same source and final conditioning event are
fixed before every query label and phase. Nonnegative complete sums
and geometric tails preserve all heights, as in
[Report572's query-profile transport](../550-599/572-compatible-fibres-lift-one-six-prime-query-law.md#unequal-fibres-can-be-retained-as-a-query-profile).
AL3 directly reuses MT11 and AR2's conditioning mechanism; it is not
a new general source or capacity theorem.

For FG7, neither available first root satisfies AR1: root0 activates
the mod5 phases0 and1 from labels5 and15, while root1 activates those
phases from labels5 and45. Choose instead r=4 or7 mod9. The15 original
lies on root0 and the45 original on leaf1 mod9, so both are inactive.
The merged cofactor inventory is exactly

    0 mod5, 2 mod25, 7 mod125, 32 mod625.                    (AL4)

It meets AL1 without the auxiliary1 mod5 guard. This proves the
conditional all-height extension for FG7 after arbitrary finite mixed
additions with j>=4 and arbitrary pure ternary additions with j>=3.
All numerical moduli remain distinct. Additions at j=0,1,2,3 must
preserve the stated full-phase test; low pure additions must preserve
the chosen leaf. In particular, j=3 is part of the hypothesis, not the
unrestricted tail. FG7 lies outside AR1 and satisfies the leaf criterion.
AR1 stops at j=2, whereas the leaf condition also tests active j=3 rows.
Both sufficient criteria remain available with their respective
hypotheses.

## No depth of a common prefix universally supplies one cofactor phase

The leaf condition is not automatic, even for irredundant families.
Consider the five actual originals

    2 mod3, 0 mod5, 6 mod15, 0 mod7, 1 mod21.              (AP1)

Their odd nonunit numerical moduli are distinct. Private witnesses
modulo105 for labels3,5,15,7,21 are respectively2,10,6,7,1. Any pure-legal
ternary prefix at depth h>=1 has first root0 or1. On root0, labels5 and15
are both active and have cofactor5 phases0 and1. On root1, labels7 and21
are both active and have cofactor7 phases0 and1. The mixed originals
already have ternary depth1, so refining within either root cannot
make that conflicting row inactive. Therefore

    for every h>=1 and every pure-legal prefix r mod3^h,
    some nonunit numerical cofactor has two active phases. (AP2)

Here active means the full original arithmetic class and the prefix
contain a common natural number. Coprime CRT makes depth-zero rows
active on every prefix; a depth-one row a mod3n is active exactly when
r mod3=a mod3. This proves AP2 at arbitrary depth without substituting
finite enumeration for the quantifier. It rules out universal existence
of a single-phase COMMON prefix, not cofactor-dependent choices,
multiple-phase suppliers or correlated survivor laws.

Indeed AP1 has a cheap actual law: normalize Haar on ternary root0,
on5-root2 and outside7-root0, and use independent Haar at11,13,17,19,23.
Its support modulo105 is{12,27,57,72,87,102}. The21 row is inactive;
the15 row has excluded5-phase1; all pure rows are avoided. Its complete
all-height product norm, including the unit, is

    (5/2)(9/4)(43/36) product_(p=11,13,17,19,23)p/(p-1)
      =4152811/442368<28.                                  (AP3)

The fixed first-root norm is1+p/(p-1), while the norm of Haar outside
one first p-root is1+p/(p-1)^2. These geometric sums supply the first
three factors. In particular,12 is an actual escaping integer; AP2 is
a source-selection obstruction, not a covering counterexample.

AP1 also already lies in the restricted nine-prime class of
[Report569 SD11--SD13](../550-599/569-complete-suffix-debits-close-the-six-prime-query-target.md#scope-and-a-restricted-original-modulus-consumer).
Its full Q6={5,7,11,13,17,19} projections have exactly the two phases0,1
at numerical cofactors5 and7, and none elsewhere. The existing two-phase
source therefore applies, including arbitrary finite added originals
supported on the first nine odd primes and touching23 or29, while
preserving distinct numerical moduli. Failure of
the single-phase common-prefix criterion does not obstruct that
already available source; no new two-phase estimate is needed here.

The existing exact consumer checks AL3, every legal FG7 root and leaf,
the complete merged phases AL4, AP1's private points and six legal
mod9 leaf conflicts, and AP3's support and rational product. Its activity
test is checked against actual common integers. A scoped Lean application
verifies AP1's distinct odd nonunit inventory, derives activity from
CRT, proves AP2 for every natural h>=1, and verifies12 escapes, using
only the standard three axioms. It is an application of existing CRT
results and adds no frozen wrapper.

A scoped Lean application also verifies the complete finite selected-leaf
counterpart of AL1--AL3. Its actual carrier is a ternary word of length
T>=2 times the seven-coordinate Q carrier, with arbitrary finite Q
heights. Originals are actual prefix pairs with injective nonzero full
depth labels. The selected leaf avoids the actual pure3/9 originals;
among all active nonunit-cofactor originals at j=0,1,2,3, equal complete
Q depth vectors must have equal complete Q phases. From these inputs the
application constructs one law null on every original and bounds every
complete finite query layout by10209527/448946<28. Queries include the
unit and absent original labels, and are chosen after the law. No source,
cap, deletion or query-budget premise is assumed.

The construction merges the actual active projections before applying
the finite Q7 supplier. It completes missing high pure ternary depths
with auxiliary prefixes, so its ternary law is supported in the actual
pure survivor but need not be uniform on that whole survivor. Its
same-product deletion bound is2804581/5049311, leaving reserve at least
2244730/5049311 before the final conditioning. The complete query bound
retains the unit exactly. Existing probability, prefix, query-completion
and conditioning results supply the application; its axiom closure is
standard and no frozen specialization is added. This check uses explicit
product-prefix coordinates; it does not verify integer CRT transport,
padding T<2, infinite-law compatibility, the complete infinite sums or
AP3's product-Haar interpretation.

The same source also has a compiled finite ninth-coordinate consumer.
Adjoin one q-letter word with q>=29 and arbitrary finite height H,
including H=0. Full original depth labels must be injective and nonunit;
only the subfamily of q-depth zero must satisfy the selected-leaf
conditions. All positive-q-depth originals have arbitrary phases, and
their old P8 cofactor may be the unit. The application chooses the old
law once, completes every fixed-q-depth original slice to a full old
query layout, and joins one uniform q-word. Each positive slice uses
the full bound C=10209527/448946, including the unit. Summing its actual
original hit probabilities gives at most C/(q-1)<1, yielding an actual
product-word point outside every original. No source, query-budget,
reserve or covering premise is supplied. This is a finite prefix-space
noncoverage result with standard axioms; it does not claim integer CRT
transport or require q to be prime. T>=2 and the q-free selected-leaf
condition remain explicit. The remaining general problem is to construct
one source that retains low-row activation correlations with a sufficient
complete-query bound when no single-phase common prefix exists.

### Arithmetic transport of the selected-leaf criterion

The selected-leaf consumer also has a scoped Lean application to actual
natural-number congruences. Fix a prime q>=29 and explicit bounded
prime-power presentations over3,5,7,11,13,17,19,23,q. The original
numerical products must be pairwise distinct and greater than one;
each has one fixed natural residue a_k. Write j_k for its3-exponent,
e_k for its q-exponent, and n_k for its COMPLETE Q7 cofactor. Select
r in{0,...,8}, and call row k active when there is a common natural
integer congruent to r modulo9 and to a_k modulo3^j_k. The application
also verifies the equivalent finite test

    active(k) iff r=a_k modulo3^min(2,j_k).

Only the q-free subfamily, e_k=0, must satisfy the following conditions.
Actual pure3/9 originals are inactive. Among active originals with
j_k<=3, equal complete numerical cofactors n_k=n_l require
a_k=a_l modulo n_k. For n_k=1 the phase condition is tautological.
All positive-q-exponent originals retain arbitrary phases, including
pure q-powers. From exactly these arithmetic inputs the application
proves that a natural number avoids EVERY original congruence.

The transport uses actual CRT witnesses to recover each original
prime-power phase, then checks the complete projection to the finite
ternary/Q7/q carrier. Bare-leaf activity is proved from the value of
the same ternary word, without an extra survival requirement. Adding
two ambient digits in every coordinate preserves the original products
and residues and supplies the required ternary height; the original
height bounds may be zero. The covering assumption is introduced only
inside the final contradiction and is not an input to the theorem.

The cache-guarded application has only the standard axiom closure and
reuses the existing CRT, prefix and finite-source results. No canonical
specialization is added. Its input includes the displayed prime-power
presentations and natural residues; automatic factorization and signed
residue normalization are not part of this check. The selected-leaf
phase condition remains a substantive restriction and does not settle
unrestricted Erdős#7.
