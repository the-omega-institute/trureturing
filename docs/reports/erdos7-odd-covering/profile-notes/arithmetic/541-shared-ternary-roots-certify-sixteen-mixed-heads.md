# Shared ternary roots certify one entropy law for sixteen mixed heads

Every actual distinct-modulus core on P={3,5,7,11,13,17,19} with at most sixteen mixed labels at most 10^9 admits the ONE uniform probability on its FULL actual survivor in [report534](534-one-entropy-budget-controls-every-pure-prime-chain.md)'s entropy-density class G. Under this same law the complete all-height query sum is strictly below

    158050/14399 < 10.977 < T=565/51.

All fixed original phases, arbitrary finite pure heights, and arbitrary deeper mixed originals remain present. The improvement comes from bounding the union of the six possible originals 3p through their common ternary root. It does not subtract a phase-overlap rebate from an unrelated actual cap sum.

The general union estimate and actual-loss budget bridge below are ordinary mathematical arguments. A new exact consumer certifies the finite numerical comparison through an infinite-label priority frontier and verifies an actual irredundant core outside report539's capacity hypothesis, with 137 successful checks. No Lean verification or resolution of unrestricted Erdős #7 is claimed.

## Complete pure source and actual mixed loss

Take an irredundant core M0 with exactly the original survivor U. All original labels removed from the core remain UNUSED query labels relative to M0. Pure originals on each prime are pairwise disjoint; a contained pure original would be redundant. Use every retained pure original, at every height, to define

    u_p=sum_(p^e in M0)p^(-e),  w_p=1-u_p,  a_p=1/w_p,
    W=product_p w_p,  rho0=product_p H_p(. | S_p),

where S_p is the actual complete pure survivor. Thus rho0 is the single product Haar law conditioned on avoiding ALL pure originals. As in [report539](539-a-weighted-mixed-inventory-certifies-one-entropy-law.md), set

    D=1/W<=Dmax=4096/935,
    K_d=d^(-1)*product_(p|d)a_p,
    F=product_p(1+a_p/(p-1)),
    b=F-1-sum_p(a_p-1),
    v=sum_(d in M0, mixed)K_d,
    A=212731/110592.

The existing full-box inequality and exact numerical-slot identity give

    b<=A,
    sum_(unused nonunit d)K_d=b-v>=0.                (SC1)

Define the ACTUAL mixed deletion probability on this same source by

    l=rho0(union_(d in M0, mixed)[a_d]_d).

Always l<=v. Assume l<1 and let r=1-l. The single complete survivor law is

    rho=rho0(. | U)=H|U/(W*r).

Every cylinder has rho mass at most K_d/r, and D_H(rho)=log[D/r]. Hence

    rho<=Dmax/(1-l) H,
    R_unused(rho)<=(b-v)/(1-l)<=(A-l)/(1-l),
    D_H(rho)<=log[Dmax/(1-l)],
    R_P(rho)<=(F-1)/(1-l)<=(Dmax-1)/(1-l).          (SC2)

The second inequality uses the two distinct facts b<=A and v>=l. It does not replace v by a sum of saturated caps in the exact identity SC1. The final inequality uses F<=Dmax, from 1+a_p/(p-1)<=(p-1)/(p-2). All query maxima are under rho, including every unused label and every removed original label; no prime or query can choose a different source law.

This is a general ACTUAL-LOSS refinement of report539. Its criterion v<=2/3 remains valid, but a bound on the actual union l can certify rho even where the available sum-of-caps estimate is larger.

## An explicit actual-loss threshold for the original G

The sufficient bound used here is

    l < ell=173/250.                               (SC3)

Since A>1, the right sides of SC2 increase with l. At ell they give

    rho density <=204800/14399 <15<Lambda,
    R_unused <=17025167/4257792 <4,
    R_P <=158050/14399 <565/51,

where alpha=7235955529/6075000000000 and Lambda=1/alpha>800 retain the original G constants. The direct query margin is exactly

    565/51-158050/14399=4405/43197>0.

The entropy comparison uses only strict rational certificates. Positive Taylor sums and a geometric Taylor remainder give

    19/7<e<68/25.

The exact comparisons

    (19/7)^8 > (204800/14399)^3,
    (68/25)^20 <800^3

therefore give

    D_H(rho)<8/3,
    log Lambda>20/3.

Consequently R_unused(rho)+D_H(rho)<20/3<log Lambda. Thus rho satisfies every condition of the SAME G: it is supported on the full actual U, its density is below Lambda, and its unused-query and entropy sum meets the original joint budget. This proof also supplies its complete query bound directly; it does not claim that its occupied mixed-query sum alone is below report534's residual constant.

## The six 3p originals form one joint ternary block

Let Q={5,7,11,13,17,19}. The six distinguished numerical labels are

    3p,  p in Q.

Write J subset Q for those whose originals are actually in M0. Their original phases stay fixed. For each p put

    c_p=(p-1)/[p(p-2)],
    u(I)=1-product_(p in I)(1-c_p),  u(empty)=0.

Partition J into J_0,J_1,J_2 by the actual residue modulo 3 of each original 3p class. Under rho0, let t_r be the mass of ternary root r, and x_p the mass of the specified p-root of the original 3p class. Complete pure conditioning gives

    0<=t_r<=2/3,   sum_r t_r=1,
    0<=x_p<=c_p.

Indeed w_3>=1/2, so any root has conditional mass at most (1/3)/w_3<=2/3. This does NOT assume a pure original of modulus 3 is present. Arbitrary deeper pure originals are included in w_3. Similarly x_p<=(1/p)/w_p<=c_p.

On a fixed ternary root, these distinguished originals use distinct other prime coordinates. Product independence of rho0 therefore gives their EXACT union probability as

    sum_(r=0)^2 t_r*[1-product_(p in J_r)(1-x_p)].

Increasing the x_p to c_p yields an upper bound. Maximizing the remaining linear expression over the capped simplex t_r<=2/3, sum t_r=1, occurs at a permutation of (2/3,1/3,0). Move every prime in the zero-weight group into either other group; u is increasing under inclusion, so this cannot lower the relaxed expression. It follows that the full block union is at most

    C(J)=max_(I subset J) [(2/3)u(I)+(1/3)u(J minus I)].       (SC4)

This is an upper bound for the same actual product probability, uniform over its fixed phases. It is not an assertion that each capped-simplex vertex or maximizing partition can be realized by a common actual pure family. The bound is not applied to an arbitrary nu in G, where the required product independence need not hold.

For example, J={5,7} gives C(J)=412/1575. The separate saturated caps total 8/45+4/35, so their difference is 16/525. This is a reduction relative to the SATURATED comparison sum. In general the actual cap sum v cannot be reduced by that fixed constant: some original cylinders can already have zero actual source mass.

## All remaining numerical labels have a finite exact priority frontier

For every mixed P-smooth numerical label define the saturated cap

    kappa(d)=d^(-1)*product_(p|d)(p-1)/(p-2).

It bounds K_d for all complete pure inventories. Exclude the six distinguished labels 3p from this numerical list. Let d_1,d_2,... enumerate the remaining mixed labels in nonincreasing kappa order, and write S_n=sum_(i=1)^n kappa(d_i), S_0=0.

Only the first sixteen such entries are needed. They can be certified without truncating the infinite label set. Start a maximum-priority queue with the 21 squarefree products pq of distinct primes in P. On removing a label d, insert every numerical successor dp, p in P, unless that integer label has already been inserted. Even the excluded six distinguished labels must have their successors inserted.

Every mixed P-smooth label is reachable from a seed. Along an edge d to dp, kappa decreases by the factor 1/p if p already divides d, and by c_p if it does not. Both factors are strictly below one. For any label not yet removed, choose a seed-to-label path and take its first unremoved vertex. Its predecessor has been expanded, or it is an initial seed, so it is in the queue; its cap is at least that of the target label. The queue maximum is therefore a global maximum over ALL remaining infinite labels. Induction proves the emitted order. Deduplication by the original integer preserves distinct numerical moduli and cannot omit that frontier vertex.

The exact first sixteen non-distinguished entries are

    45,35,63,75,105,55,99,65,
    135,117,165,77,85,147,195,95.                  (SC5)

The consumer removes only 22 labels in total, including the six distinguished ones. Its remaining queue has 103 entries; the largest remaining cap is 72/5005. This is a finite frontier certificate for a global numerical order, not an enumeration of actual phases or a cutoff of original heights.

## Every inventory of at most sixteen mixed heads satisfies SC3

Fix B=10^9 and let tau_P(B)=sum_(P-smooth d>B)1/d be the already retained complete tail. Every original mixed label above B has cap at most Dmax/d; hence the total deeper mixed deletion is at most Dmax*tau_P(B). This payment includes all actual deeper originals and may conservatively also count unused or pure labels in the tail.

If at most sixteen mixed originals are at most B, and J is their actual distinguished-prime subset, there are at most 16-|J| other shallow mixed labels. The union bound, applied AFTER the joint block SC4, gives

    l<=C(J)+S_(16-|J|)+Dmax*tau_P(B).             (SC6)

The 64 possible subsets J exhaust this finite interface. Computing C(J) over every I subset J involves 729 comparisons in total. The retained exact consumer certifies SC6<173/250 for every J. The largest relaxed value is attained with

    J=Q,  I={5,7,11,13,17},
    C(Q)=3658998898/9820936125,
    S_10=58832/184275.

Including the complete deep tail, the uniform upper bound is

    1108499761084187788008987420781630368223832492533520642803184149
    /1602214301767424051674151330001125290900354083205189610595703125
    <173/250.                                   (SC7)

There is no assertion that the maximizing RELAXED inventory and ternary weights jointly attain this value in an actual irredundant family. All 64 inequalities are upper bounds on fixed original families; no one original is permitted to choose different phases in different branches. Equations SC1--SC3 now certify one rho=H(. | U) in G and its complete query bound for every family in the stated sixteen-head class.

## An actual irredundant core separates the sufficient hypotheses

For every p in P include exactly the three pure originals

    p^(e-1) mod p^e,  e=1,2,3.

Add exactly the following eleven mixed originals. The private-point coordinates are taken modulo p^3; omitted coordinates are zero. All points refer to the one period L=product_p p^3 and the same fixed originals.

| Label d | Phase a_d | Nonzero coordinates of a private point |
| --- | --- | --- |
| 15 | 2 | x3=2, x5=2 |
| 21 | 2 | x3=2, x7=2 |
| 33 | 2 | x3=2, x11=2 |
| 45 | 38 | x3=2, x5=3 |
| 39 | 2 | x3=2, x13=2 |
| 35 | 3 | x5=3, x7=3 |
| 51 | 2 | x3=2, x17=2 |
| 63 | 38 | x3=2, x7=3 |
| 57 | 2 | x3=2, x19=2 |
| 75 | 29 | x3=2, x5=4 |
| 105 | 53 | x3=5, x5=3, x7=4 |

Each mixed private point hits its own original and avoids all other originals. Its nonzero first p-adic digits differ from 1, so it avoids all pure originals. For a pure original p^(e-1) mod p^e, use x_p=p^(e-1) and all other coordinates zero. The first-nonzero-digit rule separates the other pure originals, while every mixed original requires at least two nonzero prime coordinates. Thus every one of the 32 originals has a private integer point by CRT; the displayed family itself is irredundant. The all-zero point survives it.

There are no additional originals, so the description specifies the complete family at all heights. Its ACTUAL pure conditioning factors are

    a_p=1/(1-1/p-1/p^2-1/p^3).

For the eleven displayed mixed labels the actual capacity is

    v=1881697945217311/2771672360984296,
    v-2/3=101749113683341/8315017082952888>0.       (SC8)

This actual core meets the new at-most-sixteen-head hypothesis and fails report539's sufficient hypothesis v<=2/3. The computation uses actual finite pure factors, not saturated envelopes. It separates those two sufficient hypotheses; it does not assert that the actual union loss l exceeds 2/3, that report539's conclusion fails on this input, or that no earlier noncoverage result applies to it.

## Result boundary and verification

[Report539](539-a-weighted-mixed-inventory-certifies-one-entropy-law.md) supplies the unused-cap identity and guarantees its original capacity criterion for at most eight shallow mixed labels. SC2 connects ACTUAL union loss to that identity, and SC4 keeps the six originals' shared ternary root. Together they prove the sixteen-head conclusion without any relative-phase restriction. The count eight was not claimed to be optimal in report539, and the number sixteen is not claimed to be optimal here.

[Report540](540-pivot-layer-multiplicities-control-one-entropy-budget.md) has a different quantifier: its sufficient profiles bound EVERY law in G. Here the theorem constructs the specific uniform law on the actual full survivor. A law chosen separately in each ternary root, a marginal source without all originals, or a collection of separate query maximizers would not establish this statement.

The [new consumer](../../frontier/cover-geometry/mixed_star_capacity.py) and [result](../../frontier/cover-geometry/mixed_star_capacity.json) use the existing [tail data](../../frontier/cover-geometry/phase_resampling_arithmetic.json), pinned at SHA256 da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f. The final consumer completed with 137 successful exact checks. These cover the priority frontier, all 64 joint-block inventories, the complete deep tail, the original entropy/density constants, the direct query bound, and the explicit fixed core SC8. Each of its 32 CRT private integers is checked against all 32 original classes; this checks supplied certificates and does not search over families. Explicit exception checks remain active under Python optimization. No floating-point values decide the inequalities. No old inventory producer, original-family enumeration or Lean build was run.

Larger shallow inventories require a stronger joint deletion estimate, another supported law, or a different sufficient criterion. The six-label block only resolves a specified part of the mixed incidence structure; it does not establish a uniform law for arbitrary actual cores or settle unrestricted Erdős #7.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_star_capacity.py
```
