# Common reference phases and five-leaf weights do not remove the phase obstruction

One fixed25-original family prevents the23-slot complete-inventory certificate from [Report801](801-retained-core-intersections-reduce-shallow-phase-contracts-to23-labels.md) from becoming positive under ANY common first-digit references, ANY of the seven distinguished-prime choices, and ANY fixed nonnegative normalized distribution on the five retained ternary leaves. The largest possible repaired certificate is

    -342672179617972/9557885493591435
      =approximately-0.035852300160713765<0.             (CO1)

This is a boundary of that certificate, not a covering system. The same actual family has the explicit uncovered integer2602750151. In particular the result does not upper-bound its actual survivor mass or rule out a different source or a tighter treatment of its actual remaining inventory.

The argument retains one actual family throughout. It strengthens the distinction between a finite compatible phase contract and arbitrary shallow phases: optimizing each reference or each label separately cannot supply a common core. These are ordinary finite proofs and exact rational calculations, not new Lean verification or a resolution of unrestricted Erdős#7.

## 1. The family, source and permitted common reference choices

Let Q=(5,7,11,13,17,19,23). The actual pure originals are0 mod3 and1 mod9. There are no actual pure-q originals forq inQ, so their actual pure-survivor laws are Haar. The23 selected mixed originals are the following fixed pairs(modulus,residue):

```
(15,10), (21,7), (45,40), (33,22), (35,0), (39,13),
(63,49), (51,34), (57,19), (55,0), (105,70), (75,25),
(69,46), (65,0), (99,22), (77,0), (85,0), (117,13),
(95,0), (165,55), (91,0), (147,49), (225,175).
```

All25 moduli are odd, nonunit and pairwise distinct. Equivalently, every mixed nonternary component is0 at its complete prime-power precision. A ternary height1 label has root1; a height2 label has leaf4 mod9. In particular EVERY actual3q original has ternary root1 andq-phase0. Every mixed class with a ternary factor is contained in at least one of these seven actual3q stars.

The common period is

    M=9*25*49*11*13*17*19*23=11712375675.

Use leaves(4,7,2,5,8), with arbitrary fixed weights w=(w1,w2,w3,w4,w5)>=0 summing to1, and Haar suffixes above depth2. The source is

    lambda=lambda3(w) tensor product_(q inQ)Haar_q.    (CO2)

The weights may be chosen after seeing this entire family but must be one fixed vector, independent of the nonternary coordinates. No source or weight is selected separately for a numerical label or a query.

The allowed reference family is broader than the single core in801. Choose ANY distinguished primep inQ and ANY reference phase c_q modq independently by coordinate, then use those SAME references in every class. Set E_q={x_q=c_q modq}. The coreG_(p,c) has:

* short ternary root1: no E_p hit and at most one hit among q!=p;
* long ternary root2: no hit among q!=p, with E_p unrestricted.

This is the801 reference shape with its distinguished prime allowed to change. Its actual hit vector is ALWAYS t_q=1/q because the nonternary source in(CO2) is Haar. Changing c therefore does not change the source-mass debit polynomial at that actual vector.

The claim concerns this reference family and the full remaining-inventory estimate in801. In this example the actual pure-q inventories are empty, so the true Haar cylinder cap is1/q^j. The negative result deliberately retains801's larger universal coefficientC_q=(q-1)/(q-2); using the tighter actual coefficient1 is also outside its scope. Cores with a different shape, nonproduct sources, weights depending on q-coordinates, non-Haar suffixes, changed selected inventories or tighter union estimates remain outside the negative result.

## 2. A finite common-reference compatibility rule

The reference choice can be expressed as a finite constraint problem rather than independent local optimizations. For an actual shallow mixed cylinder3^h n with supportD=supp(n), let

    H_m={q inD: its actual first phase equals c_q}.      (CO3)

Assume its nonternary cylinder has positive source mass and all five retained leaf weights are positive. OutsideD, the all-miss event has positive probability because every reference hit has probability strictly below1. Since the core is decreasing in hits, the actual cylinder meets the core exactly when its fixed hits alone are accepted on some compatible retained leaf. Hence the exact zero-intersection clauses are:

| Actual ternary part | Condition for zero core intersection |
|---|---|
|No ternary factor|At least two primes belong to H_m.|
|Retained short root or short leaf|p belongs to H_m, or at least two non-p primes belong to H_m.|
|Retained long root or long leaf|At least one non-p prime belongs to H_m.|
|A root/leaf already excluded by the pure anchors|Automatic.|

If an actual nonternary cylinder is already null under a pure survivor law, it also contributes an automatic clause. With zero leaf weights, omit the unsupported leaves in the direct possibility test. These qualifications prevent treating an absent or null event as an incompatible positive event.

The unknowns c_q are finite-valued coordinate variables. A singleton3q or9q slot supplies a root/leaf compatibility test and a required coordinate phase. A pq slot without a ternary factor requires BOTH endpoint phases to match the one common reference. Higher supports supply the displayed threshold clauses. Thus the constraint hypergraph retains cross-label equality of phases; it does not optimize each edge separately. Pure-survivor nullity and the first phases are all finite checks on the declared common carrier.

For the displayed family, all seven3q slots are active on the short root. A singleton short-root clause can be satisfied only when q=p and c_q=0. Therefore at least six of those seven actual slots fail the zero-intersection contract for everyp,c when the short root has positive mass. This is already a finite incompatibility witness, but a quantitative estimate is needed to test whether the leakage repair can rescue the method.

## 3. Exact minimum actual union leakage over all references

Put

    P0=product_(q inQ)(1-1/q)=331776/676039,
    s=w1+w2.

On the short root, the actual selected union is exactly the event that at least one actual q-coordinate is0: all seven3q stars are present, and every other selected event on that root is contained in their union. The conditional reference-core probability is independent of c and equals

    A_p=P0[1+sum_(q!=p)1/(q-1)].                        (CO4)

Its intersection with the event that all actual q-coordinates are nonzero has mass at mostP0. Therefore the selected union E_F satisfies, on the SAME source,

    ell_(p,c,w)=lambda(G_(p,c) intersect E_F)
      >=s(A_p-P0)
      =sP0 sum_(q!=p)1/(q-1).                         (CO5)

This bound is exact. Choose ALL references c_q=0 simultaneously. On the short root, the event of no actual zero then lies inside the core, giving equality in the subtraction. On the long root, every selected ternary original is inactive. Each remaining selected pq class requires two actual zero coordinates; at least one is non-p, which the long core excludes. Thus there is no additional long-root leakage at this one common reference.

Consequently(CO5) is the exact minimum over every common reference, for everyp and every w. No separately attainable extrema are combined.

For the fixed801 weights(3/16,3/16,5/24,5/24,5/24), s=3/8. The minimum overp also occurs atp=5, because this removes the largest term1/(p-1) from the positive sum. Its value is

    min_(p,c)ell_(p,c,w)=501984/5311735
                       =approximately0.09450471456124976.         (CO6)

This exceeds the uniform positive-leakage allowance from the801 continuation. More strongly, the actual-vector repair also fails, as the next section shows. For zero short-root mass(CO5) is zero, so(CO6) must NOT be generalized to every weight vector. The all-weight conclusion instead concerns the complete repaired certificate.

## 4. The actual-vector full-inventory estimate fails for all seven cores

Retain the SAME23 selected numerical slotsF. Let

    C_q=(q-1)/(q-2), beta_D=product_(q inD)1/(q-2),
    R_(D,h)=beta_D-sum_(3^h n inF,supp(n)=D) C_D/n,      (CO7)

forh=1,2 and nonemptyD, and forh=0 when|D|>=2. Set the otherR values to zero, and beta_empty=1. All coefficients are nonnegative. These are the complete residual inventories used by801, including arbitrary omitted numerical labels and heights; they are not the much smaller actual remaining inventory of this finite25-original example.

For a chosenp, let A_D,B_D be its short/long core probabilities when hits inD are set to zero, evaluated at the ACTUAL vector t_q=1/q. With symmetric weights(a,a,b,b,b),2a+3b=1, define

    F0_D=2a A_D+3b B_D,
    F1_D=max(2a A_D,3b B_D),
    F2_D=max(a A_D,b B_D),

    L_p(a)=F0_empty
      -(1/2)sum_D beta_D F2_D
      -sum_(D,h=0,1,2)R_(D,h)Fh_D.                    (CO8)

This is the source-mass lower certificate before subtracting selected leakage. The phrase "actual vector" refers specifically tot_q=1/q: the generic cylinder coefficients in(CO7) have NOT been tightened to their actual Haar values. Its largest possible leakage-repaired value, over common references at this same actual vector, is exactly

    J_p(a)=L_p(a)-2aP0 sum_(q!=p)1/(q-1),             (CO9)

because(CO5) is attained by c=0. The following table records the original fixed law a=3/16:

| Distinguishedp | L_p(3/16) | Minimum actual union leakage | Largest repaired certificate |
|---:|---:|---:|---:|
|5|0.053019474310410|0.094504714561250|-0.041485240250840|
|7|0.040957395817107|0.109841107875837|-0.068883712058730|
|11|0.030710342246696|0.122110222527506|-0.091399880280810|
|13|0.028630393115247|0.125177501190424|-0.096547108075177|
|17|0.024580173390468|0.129011599519070|-0.104431426128602|
|19|0.023435494439791|0.130289632295286|-0.106854137855495|
|23|0.021911060480426|0.132148589060690|-0.110237528580264|

All entries are approximations to retained exact fractions. In particular the actual-vector improvement over the uniform801 source bound does not repair this family. The obstruction occurs before any complete-query,29 or large-prime-tail estimate is invoked.

## 5. Every symmetric law is covered by exact breakpoints

Since b=(1-2a)/3, the functionJ_p(a) is continuous, concave and piecewise linear on0<=a<=1/2. Its only possible nontrivial slope changes occur at

    a=B_D/[2(A_D+B_D)] for a positive R_(D,1),
    a=B_D/[3A_D+2B_D] for a positive R_(D,2)+beta_D/2.   (CO10)

These come from equality of the two root or leaf branches. Include0 and1/2. Between consecutive listed points the function is affine, so its maximum occurs at a listed point unless it is constant, in which case the endpoints also attain it. This reduces the CONTINUOUS optimization to an exact finite computation, not a mesh search.

The consumer evaluates every point both from(CO8)-(CO9) and by an independent cumulative slope calculation. All seven exact maxima are negative:

|p|Maximizinga|Maximum repaired certificate|
|---:|---:|---:|
|5|3300/18587|-342672179617972/9557885493591435|
|7|2640/15947|-4592461925151227/82722663152254125|
|11|363/2311|-877150339698091/12423890784880575|
|13|715/4633|-20031886898166914/273976090899986475|
|17|2805/18422|-190263792560371/2464704586592325|
|19|8360/55321|-256084765406168983/3271450749984492075|
|23|240/1597|-7514549399305301/94439848298570775|

The largest of these is(CO1). Endpoint laws with one empty root are included, so the statement does not assume positive mass on every leaf.

## 6. Within-root averaging extends the obstruction to every five-leaf law

For arbitrary fixed w, put s=w1+w2 and form

    wbar=(s/2,s/2,(1-s)/3,(1-s)/3,(1-s)/3).

The exact core mass, F0 and F1 depend only on the two root totals, so they agree forw andwbar. The leaf and high-ternary factors obey

    max(A_D max(w1,w2), B_D max(w3,w4,w5))
      >=max(A_D s/2, B_D(1-s)/3).                     (CO11)

Every coefficient multiplying these factors in(CO8) is nonnegative. Thus L_p(w)<=L_p(wbar). The star-union lower bound(CO5) depends only ons, so it is unchanged. Pointwise for this SAME fixed actual family,

    L_p(w)-ell_(p,c,w)
      <=L_p(wbar)-sP0 sum_(q!=p)1/(q-1)
      =J_p(s/2)<0.                                   (CO12)

This is a comparison of bounds at one given w. It does not assume that a different source maximizes each term. No symmetrization of a query comparator is needed: the repaired head certificate is already negative. Coordinate-dependent weights, nonproduct sources and altered suffix laws are not covered by(CO11).

## 7. The obstruction survives common affine normalization

The actual pure3 and9 cylinders are nonredundant and already normalized. Any residual affine mapx->ux+v on their common finite period must satisfy

    u in{1,4,7} mod9, v=1-u mod9.

It fixes the short and long roots. It fixes leaves4 and7 individually and may permute2,5,8. Therefore it cannot move the seven actual3q stars from the short root to individually convenient roots. Arbitrary w is transported with the same map, and the family of all weight vectors is closed under the induced leaf permutation.

On a q-coordinate, a common unit and translation transport EVERY actual first phase0 to the same valuev_q. The reference choices remain arbitrary. Replacing the actual common phase0 byv_q leaves the Haar probabilities and the relative equality/non-equality pattern unchanged. Unit lifts and CRT give one common affine map on the full period, not a separate rephasing per numerical label.

For exact finite verification one may reduce a reference phase to either0 or1 relative to the common actual phase: multiplication by a unit fixes actual0 and takes any nonzero reference to1. This is done once per coordinate for the whole family. The896 cases(7 distinguished primes times128 equality patterns) therefore cover every common first-digit reference. The proof also identifies why a per-label phase optimizer would be invalid: it could satisfy inconsistent singleton clauses using different choices for the same variablec_q or for the same distinguished prime.

## 8. Exact controls and the remaining research gap

The [consumer](../../../frontier/cover-geometry/refined-capped-source/common_core_phase_obstruction.py), [certificate](../../../frontier/cover-geometry/refined-capped-source/common_core_phase_obstruction_certificate.json) and [result](../../../frontier/cover-geometry/refined-capped-source/common_core_phase_obstruction.json) retain the full fixed phase list, all896 common-reference cases, the exact seven actual-vector bounds, and every active breakpoint. The conditional long-root union is enumerated using the actual no3 pair events, while the short-root union uses the actual seven-star containment. The two parts refer to one product law and one family.

The exact calculation performs88552 explicit checks, including agreement between the compatibility clauses and direct core possibility, the complete continuous maxima, and within-root averaging controls. Normal and optimized replays exit0, as does optimized replay after relocating the three artifacts together to an independent directory. Four forged input/result controls are rejected with exit1. An independent computation gives the same1652 active knot values, seven maxima and maximizing rational weights, also checking affine interpolation at extra zero-coefficient knots. Those finite checks support the universal reduction(CO3)-(CO12); no Lean theorem is claimed.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/common_core_phase_obstruction.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/common_core_phase_obstruction.py
```

Default execution recomputes and compares the adjacent retained result. Explicit `--certificate`, `--result` and `--write-result` paths support independent replay and regeneration. The program uses only the standard library and explicit checks that remain active under optimization.

The integer2602750151 is2 mod9 and1 on all displayed nonternary prime-power coordinates. It therefore avoids the two pure anchors, every short-root mixed original, and every actual no3 pair class. The consumer checks it against all25 original residues on the single common period. This prevents reading the negative certificate as a covering construction.

The concrete missing ingredient is now narrower: the seven short-root stars cannot be jointly absorbed by a core whose short root singles out only one prime, and charging the complete omitted inventories at the retained universal caps consumes more than this core can retain. Choosing references, changing its distinguished prime, or redistributing fixed leaf weights does not remove that obstruction. A stronger method must change the relevant structure or estimate—for example its core shape, source dependence, actual tighter cylinder caps, or treatment of the remaining actual unions—while maintaining one common actual family and source. The present result does not decide whether any such improvement succeeds.
