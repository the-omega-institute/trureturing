[Index](../../marked_head_profile.md) · [Actual surviving-fibre inequality](528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md) · [Same-law overlap certificates](433-chordal-overlap-certificates-and-their-exact-finite-limits.md)

# An irredundant comb separates fibre credits from supported query laws

There is an explicit finite original family for every H>=405, supported on P={3,5,7,11,13,17,19}, with ternary height H and all other original heights at most3, for which the following obstruction holds. Fix every nonternary coordinate to normalized Haar on its full actual pure-prime survivor. For any ternary probability on the actual pure3 survivor, even allowing singular laws and arbitrary tails, let mu be the resulting product conditioned on the complete original survivor set. Then

    positive exact-single-class fibre estimate
        implies R_P(mu)>19H/694>565/51.                (IC1)

Here R_P(rho)=sum_(d>1,P-smooth) max_a rho(a mod d), including every query depth. The fibre estimate uses exact individual deletion probabilities, so neither sharper cylinder caps nor additional own-coordinate avoidance credits repair this failure. Every original class has a private integer; removing redundant originals cannot remove the example.

For the very same families, overlap accounting gives actual source survivor mass above1/10, and a different fixed nonternary product source gives

    R_P(nu)<1097/128<565/51,
    nu<720 H_P.                                      (IC2)

For each H this law is fixed before every query, and retains normalized Haar on the same actual pure3 survivor. Arbitrary additional originals touching23 or29, supported on P union{23,29}, leave full Haar survivor mass above2339/8110080>1/3500. Thus(IC1) is a failure of the specified source and its single-class mass estimate, not a failure of the seven-prime query target. No unrestricted Erdős#7 result or new Lean verification is claimed. The construction and arbitrary-height arguments below are ordinary proofs; the finite rational constants and local separation facts have a separate exact verifier.

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

The [exact verifier](../../frontier/cover-geometry/fibre_credit_irredundant_comb.py) checks the displayed rational constants, side-cylinder disjointness at the nonternary cutoff, proper-support and equal-support phase separation, and every largest-coordinate mask condition. Its [result](../../frontier/cover-geometry/fibre_credit_irredundant_comb.json) retains these finite facts. Run:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre_credit_irredundant_comb.py
```

The program does not enumerate the full original CRT period or claim that a bounded sample proves the arbitrary-H statements. Those follow from the disjoint side-cylinder construction, the exact two-fibre identity and the conditioning argument above. Default execution checks the retained result; `--output PATH` writes the recomputed result. No source geometry or Lean build is used.

For arbitrary originals, report433 already supplies same-law forest and chordal overlap certificates with actual intersection masses; no new forest theorem is needed. The unresolved step is a sufficiently strong estimate of actual overlapping deletions, or a supported source change, that also controls the full query inventory for unrestricted original phases and heights. The two repairs here are verified for this explicit family, not for every seven-prime core.
